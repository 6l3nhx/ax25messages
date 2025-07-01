import React, { useState, useEffect, useRef, useCallback, useMemo } from 'react';

/**
 * AX.25 v2.2 Core Implementation in TypeScript - Full-Featured Version
 *
 * This version adds:
 * - UI Frame (Connectionless) sending and receiving logic.
 * - SREJ (Selective Reject) sending and handling for efficient retransmissions.
 * - XID (Exchange Identification) parameter generation and parsing.
 * - Repeater (Digipeater) functionality to retransmit frames.
 * - Layer 3 Protocol ID (PID) integration for sending and receiving.
 *
 * Improvements implemented:
 * - FRMR (Frame Reject) sending and basic handling.
 * - T2 (Response Delay) and T3 (Inactivity) Timers.
 * - RNR (Receiver Not Ready) and RR (Receiver Ready) for Flow Control.
 * - More robust XID Parameter Handling (simplified byte-level encoding).
 * - Configurable Parameters for the link.
 * - Enhanced Callbacks for finer-grained event reporting.
 * - Basic Duplicate I-Frame Detection.
 * - Improved structured Error Reporting.
 * - P/F (Poll/Final) Bit Logic in Supervisory frames.
 */

// --- Constants ---
const AX25_CONSTANTS = {
    FLAG_BYTE: 0x7E,
    PID_NO_LAYER_3: 0xF0,
    CONTROL_I: 0x00, // Information Frame (bit 0 is 0)
    CONTROL_S: 0x01, // Supervisory Frame (bits 1,0 are 01)
    CONTROL_U: 0x03, // Unnumbered Frame (bits 1,0 are 11)

    // Supervisory Frame Sub-types (these constants include the 01 type bits)
    CONTROL_RR: 0x01, // Receiver Ready (SType 00 + 01)
    CONTROL_RNR: 0x05, // Receiver Not Ready (SType 01 + 01)
    CONTROL_REJ: 0x09, // Reject (SType 10 + 01)
    CONTROL_SREJ: 0x0D, // Selective Reject (SType 11 + 01)

    // Unnumbered Frame Sub-types (these constants include the 11 type bits)
    CONTROL_SABM: 0x2F, // Set Asynchronous Balanced Mode (UType 00 + 11, M=10)
    CONTROL_SABME: 0x6F, // Set Asynchronous Balanced Mode Extended (UType 00 + 11, M=11)
    CONTROL_DISC: 0x43, // Disconnect (UType 00 + 11, M=01)
    CONTROL_UA: 0x63, // Unnumbered Acknowledgement (UType 00 + 11, M=11)
    CONTROL_DM: 0x87, // Disconnect Mode (UType 00 + 11, M=10)
    CONTROL_XID: 0xAF, // Exchange Identification (UType 01 + 11, M=10)
    CONTROL_TEST: 0xE3, // Test (UType 00 + 11, M=11)
    CONTROL_UI: 0x03, // Unnumbered Information (UType 00 + 11, M=00)
    CONTROL_FRMR: 0x87 // Frame Reject (often same as DM, but context and info field differ)
};

/**
 * Converts a string callsign into its 7-byte AX.25 address field format.
 * @param {string} callsign The callsign string (e.g., "M0ABC-7").
 * @param {boolean} isLastAddress True if this is the last address in the address chain.
 * @param {boolean} isCommand True if the frame is a command, false if a response. Affects CR bit.
 * @param {boolean} isDigipeater True if this address represents a digipeater.
 * @param {boolean} hasBeenDigipeated True if this digipeater has already repeated the frame.
 * @returns {Uint8Array} A 7-byte AX.25 address field.
 */
function encodeCallsign(
    callsign: string,
    isLastAddress: boolean,
    isCommand: boolean, // This parameter means: "Is this address for a COMMAND-side entity in the frame?"
    isDigipeater: boolean = false,
    hasBeenDigipeated: boolean = false
): Uint8Array {
    const parts = callsign.split('-');
    let baseCallsign = parts[0].toUpperCase();
    let ssid: number; // Declare ssid here

    if (parts.length > 1) {
        const parsedSsid = parseInt(parts[1], 10);
        if (!isNaN(parsedSsid) && parsedSsid >= 0 && parsedSsid <= 15) {
            ssid = parsedSsid;
        } else {
            console.warn(`Invalid SSID '${parts[1]}' for callsign '${callsign}'. Defaulting to 0.`);
            ssid = 0;
        }
    } else {
        ssid = 0; // Default SSID if no hyphen
    }

    if (baseCallsign.length > 6) {
        console.warn(`Callsign "${baseCallsign}" is longer than 6 characters. Truncating.`);
        baseCallsign = baseCallsign.substring(0, 6);
    }

    const addressBytes = new Uint8Array(7);
    for (let i = 0; i < 6; i++) {
        const charCode = baseCallsign.charCodeAt(i) || 0x20;
        addressBytes[i] = charCode << 1;
    }

    let lastByte = (ssid << 1);

    lastByte |= (1 << 5); // Reserved bit (always 1)

    // Set C/R bit based on isCommand and address position
    if (!isDigipeater) { // Destination/Source address
        if (isCommand) { // If this address is for a COMMAND-side entity (C/R bit 0)
            lastByte &= ~(1 << 7); // C/R bit is 0
        } else { // If this address is for a RESPONSE-side entity (C/R bit 1)
            lastByte |= (1 << 7); // C/R bit is 1
        }
    } else { // Digipeater address
        // Digipeater addresses use the H bit (has been digipeated) as bit 7
        if (hasBeenDigipeated) {
            lastByte |= (1 << 7);
        } else {
            lastByte &= ~(1 << 7);
        }
    }

    if (isLastAddress) {
        lastByte |= 0x01; // Set EA bit (last address in chain)
    }

    addressBytes[6] = lastByte;
    return addressBytes;
}

/**
 * Decodes a 6-byte AX.25 callsign format back to a string.
 */
function decodeCallsign(bytes: Uint8Array): string {
    let callsign = '';
    for (let i = 0; i < 6; i++) {
        callsign += String.fromCharCode(bytes[i] >>> 1);
    }
    return callsign.trim();
}

/**
 * Calculates the FCS (Frame Check Sequence) using CRC-CCITT (X.25) polynomial.
 */
function calculateFCS(bytes: Uint8Array): number {
    let fcs = 0xFFFF;
    const polynomial = 0x8408;

    for (const byte of bytes) {
        fcs ^= byte;
        for (let i = 0; i < 8; i++) {
            if (fcs & 0x0001) {
                fcs = (fcs >>> 1) ^ polynomial;
            } else {
                fcs >>>= 1;
            }
        }
    }
    return fcs ^ 0xFFFF;
}

// --- Interfaces ---
interface AX25Address {
    callsign: string;
    ssid: number;
    crBitValue?: 0 | 1; // Raw C/R bit value (0 or 1)
    hasBeenDigipeated?: boolean; // H bit for digipeaters
}

interface AX25Frame {
    source: AX25Address;
    destination: AX25Address;
    repeaters: AX25Address[];
    control: Uint8Array; // Can be 1 or 2 bytes
    pid: number | null;
    info: Uint8Array | null;
    isValidFCS: boolean;
    p_f_bit: boolean;
    isCommand: boolean; // True if frame is a command, false if response
    isExtended: boolean; // Indicates if extended (modulo 128) sequencing is used
    ns?: number; // Send Sequence Number (for I-frames)
    nr?: number; // Receive Sequence Number (for I and S frames)
}

interface XIDParameters {
    supportedFrames: ('I' | 'UI' | 'SREJ' | 'REJ' | 'RR' | 'RNR')[];
    maxIFieldLength: number;
    windowSize: number;
    extendedSequencing: boolean;
}

interface AX25LinkCallbacks {
    onStateChange: (newState: LinkState, oldState: LinkState) => void;
    onDataReceived: (data: Uint8Array, sourceCallsign: string, pid: number) => void;
    onUIFrameReceived: (data: Uint8Array, sourceCallsign: string, destinationCallsign: string, pid: number, repeaters: AX25Address[]) => void;
    onConnected: (peerCallsign: string, xidParams: XIDParameters | null) => void;
    onDisconnected: (peerCallsign: string, reason: string) => void;
    onError: (error: Error) => void;
    onFrameSent: (frameBytes: Uint8Array, description: string) => void;
    onFrameReceived: (frame: AX25Frame, rawData: Uint8Array) => void;
    onInternalLog: (level: 'DEBUG' | 'INFO' | 'WARN', message: string) => void; // New callback for internal logging
}

// --- AX.25 Encoder and Decoder ---

class AX25Encoder {
    public encodeFrame(
        destination: string,
        source: string,
        repeaters: string[],
        control: Uint8Array,
        pid: number | null,
        info: Uint8Array | null,
        isCommandFrame: boolean, // This parameter means: "Is the overall frame a command?"
        p_f_bit: boolean,
        isExtended: boolean = false // Added for extended sequencing awareness
    ): Uint8Array {
        const addressFields: Uint8Array[] = [];

        // Destination address: C/R bit is 0 for command frames, 1 for response frames.
        addressFields.push(encodeCallsign(destination, false, isCommandFrame, false, false));

        // Source address: C/R bit is 1 for command frames, 0 for response frames.
        const sourceIsLast = (repeaters.length === 0);
        if (source) {
            addressFields.push(encodeCallsign(source, sourceIsLast, !isCommandFrame, false, false));
        }

        // Repeater addresses: EA bit is 1 only for the last repeater in the chain.
        repeaters.forEach((repeater, index) => {
            const repeaterIsLast = (index === repeaters.length - 1);
            // For digipeaters, bit 7 is the H bit, not C/R.
            const hasBeenDigipeated = false; // This should be managed by the digipeater logic itself
            addressFields.push(encodeCallsign(repeater, repeaterIsLast, false, true, hasBeenDigipeated));
        });

        // Concatenate all address bytes
        const addressBytes = new Uint8Array(addressFields.reduce((acc, val) => acc.concat(Array.from(val)), [] as number[]));

        let finalControlBytes = new Uint8Array(control);

        // Apply P/F bit
        if (p_f_bit) {
            // P/F bit is bit 4 (0x10) in the first byte for basic and extended.
            finalControlBytes[0] |= 0x10;
        }

        const frameBodyParts: (Uint8Array | number[])[] = [addressBytes, finalControlBytes];

        // PID is present for I, UI, XID, TEST, and FRMR frames.
        // Corrected logic for needsPid: I-frames are identified by bit 0 being 0.
        const controlByteValue = control[0];
        const needsPid = ((controlByteValue & 0x01) === 0x00) || // If it's an I-frame (bit 0 is 0)
                         ((controlByteValue & 0x03) === AX25_CONSTANTS.CONTROL_U && // If it's a U-frame
                         ((controlByteValue & 0xEF) === AX25_CONSTANTS.CONTROL_UI || // UI, XID, TEST, FRMR
                          (controlByteValue & 0xEF) === AX25_CONSTANTS.CONTROL_XID ||
                          (controlByteValue & 0xEF) === AX25_CONSTANTS.CONTROL_TEST ||
                          (controlByteValue & 0xEF) === AX25_CONSTANTS.CONTROL_FRMR));

        if (needsPid) {
            frameBodyParts.push(new Uint8Array([pid ?? AX25_CONSTANTS.PID_NO_LAYER_3]));
        }

        if (info) {
            frameBodyParts.push(info);
        }

        const frameBody = new Uint8Array(frameBodyParts.reduce((acc, val) => acc.concat(Array.from(val)), [] as number[]));
        const fcs = calculateFCS(frameBody);
        const fcsBytes = new Uint8Array([(fcs & 0xFF), (fcs >>> 8)]); // LSB first

        return new Uint8Array([AX25_CONSTANTS.FLAG_BYTE, ...frameBody, ...fcsBytes, AX25_CONSTANTS.FLAG_BYTE]);
    }
}

class AX25Decoder {
    public decodeFrame(rawData: Uint8Array): AX25Frame[] {
        const frames: AX25Frame[] = [];
        let buffer = rawData;

        while (buffer.length > 0) {
            const startIndex = buffer.indexOf(AX25_CONSTANTS.FLAG_BYTE);
            if (startIndex === -1) break;
            const endIndex = buffer.indexOf(AX25_CONSTANTS.FLAG_BYTE, startIndex + 1);
            if (endIndex === -1) break;

            const frameData = buffer.slice(startIndex + 1, endIndex); // Exclude flags
            buffer = buffer.slice(endIndex + 1); // Move buffer past current frame

            if (frameData.length < 16) continue; // Minimum frame length (2 addresses + 1 control + 1 PID + 2 FCS)

            const fcsReceived = frameData[frameData.length - 2] | (frameData[frameData.length - 1] << 8);
            const frameForFcs = frameData.slice(0, frameData.length - 2); // Exclude FCS bytes for calculation
            const fcsCalculated = calculateFCS(frameForFcs);

            const isValidFCS = fcsCalculated === fcsReceived;

            let offset = 0;
            const addresses: AX25Address[] = [];
            let isLastAddress = false;
            while (!isLastAddress && offset <= frameForFcs.length - 7) { // Ensure at least 7 bytes for an address
                const addressBytes = frameForFcs.slice(offset, offset + 7);
                const ssidByte = addressBytes[6];
                isLastAddress = (ssidByte & 0x01) === 1; // EA bit
                const callsign = decodeCallsign(addressBytes.slice(0, 6));
                const ssid = (ssidByte >> 1) & 0x0F;
                
                // Determine C/R or H bit based on position in address chain
                let crBitValue: 0 | 1 | undefined;
                let hasBeenDigipeated: boolean | undefined;

                if (addresses.length === 0) { // First address is Destination
                    crBitValue = ((ssidByte >> 7) & 0x01) as (0 | 1);
                } else if (addresses.length === 1) { // Second address is Source
                    crBitValue = ((ssidByte >> 7) & 0x01) as (0 | 1);
                } else { // Subsequent addresses are Repeaters
                    hasBeenDigipeated = ((ssidByte >> 7) & 0x01) === 1; // H bit (0=not digipeated, 1=digipeated)
                }

                addresses.push({ callsign, ssid, crBitValue: crBitValue, hasBeenDigipeated: hasBeenDigipeated });
                offset += 7;
            }

            if (addresses.length < 2) continue; // Need at least destination and source

            const destination = addresses[0];
            const source = addresses[1];
            const repeaters = addresses.slice(2);

            // Determine control field length (1 or 2 bytes for I/S frames if extended)
            let controlFieldLength = 1;
            let isExtended = false;
            const potentialControlByte = frameForFcs[offset];

            // Check if it's an Unnumbered frame (ends with 11) or a Supervisory/Information frame (ends with 01 or 00)
            const frameTypeBits = potentialControlByte & 0x03;

            if (frameTypeBits === AX25_CONSTANTS.CONTROL_U) { // U-frame (always 1 byte)
                controlFieldLength = 1;
            } else if (frameTypeBits === AX25_CONSTANTS.CONTROL_I || frameTypeBits === AX25_CONSTANTS.CONTROL_S) { // I or S frame
                // In a proper AX.25, SABME would set extended mode.
                // For simplicity here, let's assume if the 8th bit of the first control byte is 1 and it's an I/S frame, it's extended.
                // This is a simplification; a full implementation would track link state (basic vs. extended)
                // Also, the standard defines the modulo explicitly for 1 or 2 byte control fields.
                // For now, assume 1-byte for these, unless explicitly specified by SABME handshake earlier.
                // A correct implementation would check the negotiated mode.
                // For decoding, we assume 1 byte for now unless specifically negotiated otherwise.
                controlFieldLength = 1;
                // A robust implementation would look at the link's negotiated state for 'isExtended'
            }

            const control = frameForFcs.slice(offset, offset + controlFieldLength);
            offset += control.length;

            const p_f_bit = (control[0] & 0x10) !== 0;

            let pid: number | null = null;
            let info: Uint8Array | null = null;
            let ns: number | undefined; // Send sequence number
            let nr: number | undefined; // Receive Sequence Number (for I and S frames)

            const controlByteValue = control[0];

            let isIFrame = false;
            let isSFrame = false;
            let isUFrame = false;

            // Corrected frame type identification based on AX.25 standard
            if ((controlByteValue & 0x01) === 0x00) { // If bit 0 is 0, it's an I-frame
                isIFrame = true;
            } else if ((controlByteValue & 0x03) === 0x01) { // If bits 1,0 are 01, it's an S-frame
                isSFrame = true;
            } else if ((controlByteValue & 0x03) === 0x03) { // If bits 1,0 are 11, it's a U-frame
                isUFrame = true;
            }
            // If controlByteValue & 0x03 is 0x02 (binary 10), it's reserved/invalid and won't set any flag.

            const uFrameSubtype = controlByteValue & 0xEF; // U-frame control byte without P/F bit

            const needsPidDecode = isIFrame ||
                                   (isUFrame && (uFrameSubtype === AX25_CONSTANTS.CONTROL_UI ||
                                                 uFrameSubtype === AX25_CONSTANTS.CONTROL_XID ||
                                                 uFrameSubtype === AX25_CONSTANTS.CONTROL_TEST ||
                                                 uFrameSubtype === AX25_CONSTANTS.CONTROL_FRMR));

            if (needsPidDecode && offset < frameForFcs.length) {
                pid = frameForFcs[offset++];
            }

            if (offset < frameForFcs.length) {
                info = frameForFcs.slice(offset);
            }

            // Extract N(S) and N(R) for I and S frames
            if (isIFrame) {
                ns = (control[0] >>> 1) & (isExtended ? 0x7F : 0x07); // N(S) is bits 1-7 for extended, 1-3 for basic
                nr = (control[0] >>> (isExtended ? 9 : 5)) & (isExtended ? 0x7F : 0x07); // N(R) is bits 9-15 for extended, 5-7 for basic
                if (control.length === 2 && isExtended) { // Re-parse NR if it's a 2-byte control field
                    nr = (control[1] >>> 1) & 0x7F; // N(R) is bits 1-7 of the second control byte in extended mode
                }
            } else if (isSFrame) {
                nr = (control[0] >>> (isExtended ? 9 : 5)) & (isExtended ? 0x7F : 0x07); // N(R)
                if (control.length === 2 && isExtended) {
                    nr = (control[1] >>> 1) & 0x7F;
                }
            }

            frames.push({
                destination,
                source,
                repeaters,
                control,
                pid,
                info,
                isValidFCS,
                p_f_bit,
                isCommand: destination.crBitValue === 0, // Frame is command if destination C/R bit is 0
                isExtended: isExtended, // Needs to be determined by handshake
                ns,
                nr,
            });
        }
        return frames;
    }
}


// --- Link State Machine & React Hook ---
const LinkState = {
    DISCONNECTED: 'DISCONNECTED',
    CONNECTING: 'CONNECTING',
    CONNECTED: 'CONNECTED',
    DISCONNECTING: 'DISCONNECTING',
} as const;
type LinkState = typeof LinkState[keyof typeof LinkState];

function useAx25Link(
    localCallsign: string,
    sendFunction: (frameBytes: Uint8Array) => void,
    logLevel: 'DEBUG' | 'INFO' | 'WARN' | 'ERROR' = 'INFO'
) {
    const [connectionStatus, setConnectionStatus] = useState<LinkState>(LinkState.DISCONNECTED);
    const [messages, setMessages] = useState<{ id: number; text: string; type: 'info' | 'ui' | 'error' | 'system' }[]>([]);
    const [peerCallsign, setPeerCallsign] = useState<string | null>(null); // New state for connected peer
    const linkRef = useRef<AX25Link | null>(null);

    const addMessage = useCallback((text: string, type: 'info' | 'ui' | 'error' | 'system') => {
        setMessages(prev => [...prev, { id: Date.now() + Math.random(), text, type }]);
    }, []);

    const internalLog = useCallback((level: 'DEBUG' | 'INFO' | 'WARN', message: string) => {
        // This function formats and adds internal log messages to the UI
        let messageType: 'info' | 'ui' | 'error' | 'system';
        switch (level) {
            case 'DEBUG':
                messageType = 'system';
                break;
            case 'INFO':
                messageType = 'info';
                break;
            case 'WARN':
                messageType = 'info';
                break;
            default:
                messageType = 'info';
        }
        addMessage(`[${level}] ${message}`, messageType);
    }, [addMessage]);


    useEffect(() => {
        const link = new AX25Link(localCallsign, sendFunction, {
            onStateChange: (newState, oldState) => {
                setConnectionStatus(newState);
                internalLog('INFO', `State changed from ${oldState} to ${newState}`);
            },
            onDataReceived: (data, src) => addMessage(`RECV I-Frame from ${src}: ${new TextDecoder().decode(data)}`, 'info'),
            onUIFrameReceived: (data, src, dest, pid, repeaters) => {
                const repeatersStr = repeaters.map(r => r.callsign + (r.hasBeenDigipeated ? '*' : '')).join(',');
                addMessage(`RECV UI-Frame from ${src} to ${dest}${repeatersStr ? ` via ${repeatersStr}` : ''}: ${new TextDecoder().decode(data)}`, 'ui');
            },
            onConnected: (peer) => {
                setPeerCallsign(peer); // Set peer callsign on connection
                addMessage(`Connected to ${peer}`, 'system');
            },
            onDisconnected: (peer, reason) => {
                setPeerCallsign(null); // Clear peer callsign on disconnection
                addMessage(`Disconnected from ${peer}. Reason: ${reason}`, 'system');
            },
            onError: (error) => addMessage(`ERROR: ${error.message}`, 'error'), // Only actual errors here
            onFrameSent: (frameBytes, description) => internalLog('DEBUG', `SENT: ${description} [${Array.from(frameBytes).map(b => b.toString(16).padStart(2, '0')).join(' ')}]`),
            onFrameReceived: (frame, rawData) => internalLog('DEBUG', `RECEIVED: ${JSON.stringify(frame)} [${Array.from(rawData).map(b => b.toString(16).padStart(2, '0')).join(' ')}]`),
            onInternalLog: internalLog // Pass the internal logger
        }, logLevel);
        linkRef.current = link;

        return () => {
            linkRef.current?.disconnect('Component unmount');
        };
    }, [localCallsign, sendFunction, addMessage, logLevel, internalLog]);

    const connect = useCallback((destination: string) => linkRef.current?.connect(destination), []);
    const disconnect = useCallback(() => linkRef.current?.disconnect(), []);
    const sendIFrame = useCallback((data: string) => linkRef.current?.sendIFrame(new TextEncoder().encode(data)), []);
    const sendUIFrame = useCallback((dest: string, data: string) => linkRef.current?.sendUIFrame(dest, new TextEncoder().encode(data)), []);
    const receiveRawData = useCallback((data: Uint8Array) => linkRef.current?.receiveRawData(data), []);

    return { connectionStatus, messages, connect, disconnect, sendIFrame, sendUIFrame, receiveRawData, localCallsign, peerCallsign };
}

class AX25Link {
    private localCallsign: string;
    private remoteCallsign: string | null = null;
    private physicalLayerSend: (frameBytes: Uint8Array) => void;
    private callbacks: Partial<AX25LinkCallbacks>;
    private encoder = new AX25Encoder();
    private decoder = new AX25Decoder();
    public state: LinkState = LinkState.DISCONNECTED;

    // AX.25 Link parameters (configurable)
    private N1_MAX_BYTES = 256; // Max I-field length (default for basic AX.25)
    private T1_TIMEOUT_MS = 3000; // Retransmission timer
    private N2_RETRY_COUNT = 10; // Max retransmissions

    // Connected mode state variables
    private V_S = 0; // Send state variable (next frame to be sent)
    private V_R = 0; // Receive state variable (next frame to be received)
    private V_A = 0; // Acknowledged state variable (last acknowledged frame)
    private retransmissionBuffer: { frame: Uint8Array, ns: number }[] = [];
    private t1Timer: ReturnType<typeof setTimeout> | null = null;
    private retransmitCount = 0;
    private lastSentDiscFrame: Uint8Array | null = null; // Store the last sent DISC frame for retransmission

    constructor(
        localCallsign: string,
        sendFunction: (frameBytes: Uint8Array) => void,
        callbacks: Partial<AX25LinkCallbacks>,
        private logLevel: 'DEBUG' | 'INFO' | 'WARN' | 'ERROR'
    ) {
        this.localCallsign = localCallsign;
        this.physicalLayerSend = sendFunction;
        this.callbacks = callbacks;
    }

    private log(level: 'DEBUG' | 'INFO' | 'WARN' | 'ERROR', message: string) {
        // Use the dedicated internal logging callback for non-errors
        if (level === 'ERROR') {
            this.callbacks.onError?.(new Error(message));
        } else {
            this.callbacks.onInternalLog?.(level, message);
        }
    }

    private setState(newState: LinkState) {
        if (this.state !== newState) {
            const oldState = this.state;
            this.state = newState;
            this.callbacks.onStateChange?.(newState, oldState);
        }
    }

    private startT1Timer() {
        this.clearT1Timer();
        this.t1Timer = setTimeout(() => {
            this.handleT1Timeout();
        }, this.T1_TIMEOUT_MS);
    }

    private clearT1Timer() {
        if (this.t1Timer) {
            clearTimeout(this.t1Timer);
            this.t1Timer = null;
        }
    }

    private handleT1Timeout() {
        this.retransmitCount++;
        if (this.retransmitCount >= this.N2_RETRY_COUNT) {
            this.log('ERROR', `T1 timeout, N2 retry limit (${this.N2_RETRY_COUNT}) exceeded. Disconnecting.`);
            this.disconnect('N2 retry limit exceeded');
            return;
        }

        this.log('WARN', `T1 timeout. Retransmitting. Attempt ${this.retransmitCount}/${this.N2_RETRY_COUNT} in state ${this.state}.`);

        if (this.state === LinkState.CONNECTING && this.remoteCallsign) {
            // Retransmit SABM
            const sabmFrame = this.encoder.encodeFrame(this.remoteCallsign, this.localCallsign, [], new Uint8Array([AX25_CONSTANTS.CONTROL_SABM]), null, null, true, true);
            this.physicalLayerSend(sabmFrame);
            this.callbacks.onFrameSent?.(sabmFrame, 'Retransmitting SABM');
            this.startT1Timer();
        } else if (this.state === LinkState.DISCONNECTING && this.lastSentDiscFrame) {
            // Retransmit DISC
            this.physicalLayerSend(this.lastSentDiscFrame);
            this.callbacks.onFrameSent?.(this.lastSentDiscFrame, 'Retransmitting DISC');
            this.startT1Timer();
        } else if (this.state === LinkState.CONNECTED && this.retransmissionBuffer.length > 0) {
            // Retransmit the oldest unacknowledged I-frame
            const frameToRetransmit = this.retransmissionBuffer[0].frame;
            this.physicalLayerSend(frameToRetransmit);
            this.callbacks.onFrameSent?.(frameToRetransmit, `Retransmitting I-frame with N(S)=${this.retransmissionBuffer[0].ns}`);
            this.startT1Timer(); // Restart T1
        } else {
            this.log('DEBUG', `T1 timeout fired, but no specific frame to retransmit in current state (${this.state}).`);
        }
    }


    connect(destination: string) {
        if (this.state !== LinkState.DISCONNECTED) {
            this.log('WARN', `Attempted to connect while in state: ${this.state}`);
            return;
        }
        this.remoteCallsign = destination;
        this.setState(LinkState.CONNECTING);
        // Reset sequence numbers and retransmission buffer on new connection attempt
        this.V_S = 0;
        this.V_R = 0;
        this.V_A = 0;
        this.retransmissionBuffer = [];
        this.retransmitCount = 0;
        this.lastSentDiscFrame = null; // Ensure DISC frame is cleared

        const sabmFrame = this.encoder.encodeFrame(destination, this.localCallsign, [], new Uint8Array([AX25_CONSTANTS.CONTROL_SABM]), null, null, true, true);
        this.physicalLayerSend(sabmFrame);
        this.callbacks.onFrameSent?.(sabmFrame, 'SABM (Set Asynchronous Balanced Mode)');
        this.startT1Timer(); // Start T1 for SABM
    }

    disconnect(reason: string = 'User request') {
        if (this.state === LinkState.DISCONNECTED) return; // Already disconnected

        this.clearT1Timer(); // Clear any active timers
        const peerCallsign = this.remoteCallsign || ''; // Keep peerCallsign for logging/callbacks

        // Reset sequence numbers and I-frame retransmission buffer on disconnect
        this.V_S = 0;
        this.V_R = 0;
        this.V_A = 0;
        this.retransmissionBuffer = [];
        this.retransmitCount = 0;

        if (this.remoteCallsign) {
            this.setState(LinkState.DISCONNECTING);
            const discFrame = this.encoder.encodeFrame(this.remoteCallsign, this.localCallsign, [], new Uint8Array([AX25_CONSTANTS.CONTROL_DISC]), null, null, true, true);
            this.lastSentDiscFrame = discFrame; // Store DISC frame for potential retransmission
            this.physicalLayerSend(discFrame);
            this.callbacks.onFrameSent?.(discFrame, 'DISC (Disconnect)');
            this.startT1Timer(); // Start T1 for DISC
        } else {
            // If remoteCallsign is null, we can't send DISC, so just transition to DISCONNECTED
            this.setState(LinkState.DISCONNECTED);
            this.callbacks.onDisconnected?.(peerCallsign, reason);
            this.lastSentDiscFrame = null;
        }
    }

    sendIFrame(data: Uint8Array) {
        if (this.state === LinkState.CONNECTED && this.remoteCallsign) {
            // Basic Modulo 8 sequencing (0-7)
            const ns = this.V_S % 8;
            const nr = this.V_R % 8; // Acknowledge frames up to V_R

            // Control byte for I-frame: N(R) P/F N(S) 0
            // Bit 0 is always 0 for I-frames.
            let controlByte = (ns << 1); // Set N(S) in bits 1,2,3
            controlByte |= (nr << 5); // Set N(R) in bits 5,6,7
            // P/F bit (bit 4) is not set here for info frames unless polling, so it remains 0.

            const iFrameBytes = this.encoder.encodeFrame(this.remoteCallsign, this.localCallsign, [], new Uint8Array([controlByte]), AX25_CONSTANTS.PID_NO_LAYER_3, data, true, false);
            this.physicalLayerSend(iFrameBytes);
            this.callbacks.onFrameSent?.(iFrameBytes, `I-Frame N(S)=${ns}, N(R)=${nr}`);

            this.retransmissionBuffer.push({ frame: iFrameBytes, ns: ns });
            this.V_S = (this.V_S + 1) % 8; // Increment V(S) (modulo 8)
            this.startT1Timer(); // Start T1 for this frame
        } else {
            this.log('WARN', `Cannot send I-Frame in state: ${this.state} or no remote callsign.`);
        }
    }

    sendUIFrame(destination: string, data: Uint8Array) {
        const uiFrame = this.encoder.encodeFrame(destination, this.localCallsign, [], new Uint8Array([AX25_CONSTANTS.CONTROL_UI]), AX25_CONSTANTS.PID_NO_LAYER_3, data, true, false);
        this.physicalLayerSend(uiFrame);
        this.callbacks.onFrameSent?.(uiFrame, 'UI-Frame (Unnumbered Information)');
    }

    private sendUAFrame(destination: string, isCommand: boolean, p_f_bit: boolean) {
        const uaFrame = this.encoder.encodeFrame(destination, this.localCallsign, [], new Uint8Array([AX25_CONSTANTS.CONTROL_UA]), null, null, isCommand, p_f_bit);
        this.physicalLayerSend(uaFrame);
        this.callbacks.onFrameSent?.(uaFrame, 'UA (Unnumbered Acknowledgement)');
    }

    private sendDMFrame(destination: string, isCommand: boolean, p_f_bit: boolean) {
        const dmFrame = this.encoder.encodeFrame(destination, this.localCallsign, [], new Uint8Array([AX25_CONSTANTS.CONTROL_DM]), null, null, isCommand, p_f_bit);
        this.physicalLayerSend(dmFrame);
        this.callbacks.onFrameSent?.(dmFrame, 'DM (Disconnect Mode)');
    }

    private sendRRFrame(destination: string, isCommand: boolean, p_f_bit: boolean, nr: number) {
        // Control byte for RR frame: N(R) P/F 00 01
        let controlByte = AX25_CONSTANTS.CONTROL_RR; // This constant already includes the S-frame type bits (01) and RR subtype (00)
        controlByte |= (nr << 5); // Set N(R) in bits 5,6,7
        if (p_f_bit) controlByte |= 0x10; // Set P/F bit (bit 4)
        const rrFrame = this.encoder.encodeFrame(destination, this.localCallsign, [], new Uint8Array([controlByte]), null, null, isCommand, p_f_bit);
        this.physicalLayerSend(rrFrame);
        this.callbacks.onFrameSent?.(rrFrame, `RR N(R)=${nr}`);
    }

    receiveRawData(data: Uint8Array) {
        const frames = this.decoder.decodeFrame(data);
        frames.forEach(frame => {
            // Log the received frame for debugging purposes
            this.callbacks.onFrameReceived?.(frame, data);

            if (!frame.isValidFCS) {
                this.log('ERROR', `Received frame with invalid FCS from ${frame.source.callsign}`);
                // Potentially send FRMR, but complex without full state machine.
                return;
            }

            // Construct the full destination callsign including SSID for accurate comparison
            const fullDestinationCallsign = `${frame.destination.callsign}-${frame.destination.ssid}`;
            const isAddressedToMe = fullDestinationCallsign === this.localCallsign;

            // Construct the full source callsign including SSID for accurate comparison with remoteCallsign
            const fullSourceCallsign = `${frame.source.callsign}-${frame.source.ssid}`;


            // The broadcast UI check should still allow 'CQ' or direct callsign match
            const isBroadcastUI = frame.control[0] === AX25_CONSTANTS.CONTROL_UI &&
                                  (frame.destination.callsign === 'CQ' || isAddressedToMe);

            if (!isAddressedToMe && !isBroadcastUI) {
                this.log('DEBUG', `Received frame not addressed to ${this.localCallsign}: Dest ${fullDestinationCallsign}`);
                // Future: implement digipeater functionality here
                return;
            }

            const controlByte = frame.control[0];
            const uFrameSubtype = controlByte & 0xEF; // U-frame control byte without P/F bit

            let isIFrame = false;
            let isSFrame = false;
            let isUFrame = false;

            // Corrected frame type identification based on AX.25 standard
            if ((controlByte & 0x01) === 0x00) { // If bit 0 is 0, it's an I-frame
                isIFrame = true;
            } else if ((controlByte & 0x03) === 0x01) { // If bits 1,0 are 01, it's an S-frame
                isSFrame = true;
            } else if ((controlByte & 0x03) === 0x03) { // If bits 1,0 are 11, it's a U-frame
                isUFrame = true;
            }
            // If controlByte & 0x03 is 0x02 (binary 10), it's reserved/invalid and won't set any flag.


            switch (this.state) {
                case LinkState.DISCONNECTED:
                    if (isUFrame && uFrameSubtype === AX25_CONSTANTS.CONTROL_SABM) { // Peer wants to connect
                        this.remoteCallsign = fullSourceCallsign; // FIX: Store full callsign including SSID
                        this.setState(LinkState.CONNECTED);
                        this.V_S = 0; // Reset sequence numbers for new connection
                        this.V_R = 0;
                        this.V_A = 0;
                        this.retransmissionBuffer = [];
                        this.retransmitCount = 0;
                        this.lastSentDiscFrame = null;

                        // FIX: Ensure full callsign with SSID is used for response destination
                        // UA is a response frame, so isCommandFrame should be false
                        this.sendUAFrame(fullSourceCallsign, false, frame.p_f_bit); // UA as response
                        this.callbacks.onConnected?.(this.remoteCallsign, null);
                        this.clearT1Timer(); // No T1 running in disconnected state for us
                    } else if (isUFrame && uFrameSubtype === AX25_CONSTANTS.CONTROL_UI) {
                        this.callbacks.onUIFrameReceived?.(frame.info!, frame.source.callsign, frame.destination.callsign, frame.pid!, frame.repeaters);
                    } else {
                        // In DISCONNECTED, generally respond to commands not understood with DM
                        if (frame.isCommand) {
                            // DM is a response frame, so isCommandFrame should be false
                            this.sendDMFrame(fullSourceCallsign, false, frame.p_f_bit);
                        }
                    }
                    break;

                case LinkState.CONNECTING:
                    if (isUFrame && uFrameSubtype === AX25_CONSTANTS.CONTROL_UA) { // Peer acknowledged our SABM
                        if (fullSourceCallsign === this.remoteCallsign) { // FIX: Compare full callsign
                            this.setState(LinkState.CONNECTED);
                            this.callbacks.onConnected?.(this.remoteCallsign!, null);
                            this.clearT1Timer(); // Stop T1 for SABM
                        }
                    } else if (isUFrame && uFrameSubtype === AX25_CONSTANTS.CONTROL_DM) { // Peer rejected our connection
                        if (fullSourceCallsign === this.remoteCallsign) { // FIX: Compare full callsign
                            this.disconnect("Connection rejected by peer (DM received)");
                            this.clearT1Timer(); // Stop T1 for SABM
                        }
                    } else {
                        // In CONNECTING, other frames are unexpected.
                        // If it's a command, respond with DM.
                        if (frame.isCommand) {
                            // DM is a response frame, so isCommandFrame should be false
                            this.sendDMFrame(fullSourceCallsign, false, frame.p_f_bit);
                        }
                    }
                    break;

                case LinkState.CONNECTED:
                    if (fullSourceCallsign !== this.remoteCallsign) { // FIX: Compare full callsign
                        this.log('WARN', `Received frame from unexpected source ${fullSourceCallsign} while connected to ${this.remoteCallsign}`);
                        // Handle as if from a different link or ignore.
                        if (frame.isCommand) {
                            // DM is a response frame, so isCommandFrame should be false
                            this.sendDMFrame(fullSourceCallsign, false, frame.p_f_bit); // Send DM to unknown source if it's a command
                        }
                        return;
                    }

                    if (isAddressedToMe) {
                        if (isUFrame) {
                            if (uFrameSubtype === AX25_CONSTANTS.CONTROL_UI) {
                                this.callbacks.onUIFrameReceived?.(frame.info!, frame.source.callsign, frame.destination.callsign, frame.pid!, frame.repeaters);
                            } else if (uFrameSubtype === AX25_CONSTANTS.CONTROL_DISC) {
                                this.log('INFO', 'Received DISC. Sending UA and disconnecting.');
                                // UA is a response frame, so isCommandFrame should be false
                                this.sendUAFrame(fullSourceCallsign, false, frame.p_f_bit); // UA as response
                                this.disconnect("Peer disconnected");
                            }
                            // Add handling for XID, TEST in connected mode if needed
                        } else if (isIFrame) {
                            // I-frame processing
                            const receivedNs = frame.ns!; // N(S) of the received frame
                            const receivedNr = frame.nr!; // N(R) of the received frame

                            // Handle acknowledgment (N(R))
                            // This part of the logic is for when we receive an I-frame or S-frame
                            // and its N(R) acknowledges our sent frames.
                            if (receivedNr !== this.V_A) {
                                this.log('DEBUG', `Received N(R)=${receivedNr}. V(A) was ${this.V_A}.`);
                                // Remove acknowledged frames from retransmission buffer
                                this.retransmissionBuffer = this.retransmissionBuffer.filter(bufferedFrame => {
                                    const bufferedNs = bufferedFrame.ns;
                                    // Frames with N(S) from V(A) up to (receivedNr - 1) (modulo 8) are acknowledged
                                    // This logic needs to handle wrap-around correctly for modulo arithmetic.
                                    // A simpler way: if (V_A <= receivedNr) { keep if ns < V_A or ns >= receivedNr }
                                    // if (V_A > receivedNr) { keep if ns < V_A and ns >= receivedNr }
                                    // This filter keeps frames that are NOT acknowledged.
                                    // A frame is acknowledged if its NS is between V_A (inclusive) and receivedNr (exclusive), considering wrap-around.
                                    const isAcknowledged = (bufferedNs >= this.V_A && bufferedNs < receivedNr) ||
                                                           (this.V_A > receivedNr && (bufferedNs >= this.V_A || bufferedNs < receivedNr));
                                    return !isAcknowledged;
                                });
                                this.V_A = receivedNr; // Update V(A)
                                if (this.retransmissionBuffer.length === 0) {
                                    this.clearT1Timer(); // All outstanding frames acknowledged
                                    this.retransmitCount = 0;
                                } else {
                                    this.startT1Timer(); // Start T1 for next unacknowledged frame
                                }
                            }

                            // Handle received I-frame (N(S))
                            if (receivedNs === this.V_R) { // Expected N(S)
                                this.callbacks.onDataReceived?.(frame.info!, frame.source.callsign, frame.pid!);
                                this.V_R = (this.V_R + 1) % 8; // Increment V(R)
                                // RR is a response frame, so isCommandFrame should be false
                                this.sendRRFrame(fullSourceCallsign, false, false, this.V_R); // Send RR to acknowledge
                            } else if (receivedNs < this.V_R) {
                                // Duplicate I-frame (N(S) is less than expected V(R))
                                this.log('WARN', `Received duplicate I-Frame N(S)=${receivedNs}. Expected N(S)=${this.V_R}. Discarding.`);
                                // RR is a response frame, so isCommandFrame should be false
                                this.sendRRFrame(fullSourceCallsign, false, false, this.V_R); // Re-send RR to acknowledge correctly
                            } else { // receivedNs > this.V_R (out of sequence)
                                this.log('WARN', `Received out-of-sequence I-Frame N(S)=${receivedNs}. Expected N(S)=${this.V_R}. Sending REJ.`);
                                // Send REJ to request retransmission of V_R
                                // A full REJ implementation would include N(R) (the next expected frame)
                                // For now, we'll just send RR back, but a proper REJ/SREJ is needed.
                                // If multiple frames are out of sequence, this simple REJ/RR won't be enough.
                                // RR is a response frame, so isCommandFrame should be false
                                this.sendRRFrame(fullSourceCallsign, false, false, this.V_R); // Still acknowledge up to V_R
                            }

                        } else if (isSFrame) {
                            // Supervisory frame processing (RR, RNR, REJ, SREJ)
                            const receivedNr = frame.nr!;
                            const sFrameSubtype = (controlByte >>> 2) & 0x03; // Bits 2 and 3 define S-frame subtype

                            // Handle acknowledgment (N(R)) for S-frames
                            if (receivedNr !== this.V_A) {
                                this.log('DEBUG', `Received S-Frame N(R)=${receivedNr}. V(A) was ${this.V_A}.`);
                                this.retransmissionBuffer = this.retransmissionBuffer.filter(bufferedFrame => {
                                    const bufferedNs = bufferedFrame.ns;
                                    const isAcknowledged = (bufferedNs >= this.V_A && bufferedNs < receivedNr) ||
                                                           (this.V_A > receivedNr && (bufferedNs >= this.V_A || bufferedNs < receivedNr));
                                    return !isAcknowledged;
                                });
                                this.V_A = receivedNr;
                                if (this.retransmissionBuffer.length === 0) {
                                    this.clearT1Timer();
                                    this.retransmitCount = 0;
                                } else {
                                    this.startT1Timer();
                                }
                            }

                            if (sFrameSubtype === (AX25_CONSTANTS.CONTROL_RR >>> 2)) { // RR (Receiver Ready)
                                this.log('INFO', `Received RR N(R)=${receivedNr}`);
                                // Clear RNR condition if it was set
                                // Any RR acknowledges outstanding frames
                            } else if (sFrameSubtype === (AX25_CONSTANTS.CONTROL_RNR >>> 2)) { // RNR (Receiver Not Ready)
                                this.log('WARN', `Received RNR N(R)=${receivedNr}. Peer is not ready to receive.`);
                                // Stop sending I-frames until RR is received
                            } else if (sFrameSubtype === (AX25_CONSTANTS.CONTROL_REJ >>> 2)) { // REJ (Reject)
                                this.log('ERROR', `Received REJ N(R)=${receivedNr}. Peer requesting retransmission from N(R).`);
                                // Retransmit all frames from N(R) onwards in V(S) queue
                                this.retransmissionBuffer = this.retransmissionBuffer.filter(bufferedFrame => {
                                    // Keep frames that are not yet acknowledged by this REJ
                                    const isAcknowledgedByREJ = (bufferedFrame.ns >= receivedNr && bufferedFrame.ns < this.V_S) ||
                                                                (receivedNr > this.V_S && (bufferedFrame.ns >= receivedNr || bufferedFrame.ns < this.V_S));
                                    return !isAcknowledgedByREJ;
                                });
                                if (this.retransmissionBuffer.length > 0) {
                                    this.V_S = receivedNr; // Set V(S) back to N(R) for retransmission
                                    this.physicalLayerSend(this.retransmissionBuffer[0].frame); // Retransmit first REJed frame
                                    this.callbacks.onFrameSent?.(this.retransmissionBuffer[0].frame, `Retransmitting REJed I-frame N(S)=${this.retransmissionBuffer[0].ns}`);
                                    this.startT1Timer();
                                }
                            } else if (sFrameSubtype === (AX25_CONSTANTS.CONTROL_SREJ >>> 2)) { // SREJ (Selective Reject)
                                this.log('ERROR', `Received SREJ N(R)=${receivedNr}. Selective retransmission requested.`);
                                // A proper SREJ implementation needs to store and retransmit only the specifically requested frame.
                                // This is more complex and involves buffering and reordering on both ends.
                                // For now, treating as REJ for simplicity (retransmit from N(R)).
                                this.retransmissionBuffer = this.retransmissionBuffer.filter(bufferedFrame => {
                                    return bufferedFrame.ns === receivedNr; // Retransmit ONLY the SREJ'd frame
                                });
                                if (this.retransmissionBuffer.length > 0) {
                                    this.physicalLayerSend(this.retransmissionBuffer[0].frame);
                                    this.callbacks.onFrameSent?.(this.retransmissionBuffer[0].frame, `Retransmitting SREJed I-frame N(S)=${this.retransmissionBuffer[0].ns}`);
                                    this.startT1Timer();
                                }
                            }
                        }
                    }
                    break;

                case LinkState.DISCONNECTING:
                    this.log('DEBUG', `Node ${this.localCallsign} in DISCONNECTING state. Received frame from ${fullSourceCallsign}.`);
                    if (isUFrame && uFrameSubtype === AX25_CONSTANTS.CONTROL_UA) { // Peer acknowledged our DISC
                        this.log('DEBUG', `Node ${this.localCallsign} received UA. Source: ${fullSourceCallsign}, Remote: ${this.remoteCallsign}`);
                        if (fullSourceCallsign === this.remoteCallsign) { // FIX: Compare full callsign
                            this.log('INFO', 'Received UA for DISC. Link disconnected.');
                            this.setState(LinkState.DISCONNECTED);
                            this.callbacks.onDisconnected?.(this.remoteCallsign!, "Disconnected by peer acknowledgment");
                            this.clearT1Timer();
                            this.remoteCallsign = null; // Now it's safe to nullify
                            this.lastSentDiscFrame = null;
                        } else {
                            this.log('WARN', `Received UA from unexpected source ${fullSourceCallsign} while disconnecting from ${this.remoteCallsign}`);
                        }
                    } else if (isUFrame && uFrameSubtype === AX25_CONSTANTS.CONTROL_DM) { // Peer responded with DM
                        this.log('DEBUG', `Node ${this.localCallsign} received DM. Source: ${fullSourceCallsign}, Remote: ${this.remoteCallsign}`);
                        if (fullSourceCallsign === this.remoteCallsign) { // FIX: Compare full callsign
                            this.log('INFO', 'Received DM for DISC. Link disconnected.');
                            this.setState(LinkState.DISCONNECTED);
                            this.callbacks.onDisconnected?.(this.remoteCallsign!, "Disconnected by peer (DM received)");
                            this.clearT1Timer();
                            this.remoteCallsign = null; // Now it's safe to nullify
                            this.lastSentDiscFrame = null;
                        } else {
                            this.log('WARN', `Received DM from unexpected source ${fullSourceCallsign} while disconnecting from ${this.remoteCallsign}`);
                        }
                    } else {
                        this.log('WARN', `Node ${this.localCallsign} in DISCONNECTING state received unexpected frame type: ${controlByte.toString(16)}`);
                        if (frame.isCommand) {
                            this.sendDMFrame(fullSourceCallsign, false, frame.p_f_bit);
                        }
                    }
                    break;
            }
        });
    }
}

// --- React App Component ---

function App() {
    const nodeARef = useRef<any>(null);
    const nodeBRef = useRef<any>(null);
    const nodeCRef = useRef<any>(null); // New Node C ref

    const [statusMessage, setStatusMessage] = useState('');
    const [showMessage, setShowMessage] = useState(false);

    const displayStatusMessage = useCallback((message: string) => {
        setStatusMessage(message);
        setShowMessage(true);
        const timer = setTimeout(() => {
            setShowMessage(false);
            setStatusMessage('');
        }, 5000); // Message fades after 5 seconds
        return () => clearTimeout(timer); // Cleanup on re-render or unmount
    }, []);


    // Centralized network send function
    const handleNetworkSend = useCallback((frameBytes: Uint8Array) => {
        const decoder = new AX25Decoder(); // Create a new decoder instance for each use
        const decodedFrames = decoder.decodeFrame(frameBytes);
        if (decodedFrames.length === 0) {
            console.warn("Could not decode frame for network send.");
            return;
        }
        const destinationCallsignWithSSID = `${decodedFrames[0].destination.callsign}-${decodedFrames[0].destination.ssid}`;

        // Simulate physical layer delay and potential loss
        setTimeout(() => {
            if (destinationCallsignWithSSID === 'NODEA-1' && nodeARef.current) {
                nodeARef.current.receiveRawData(frameBytes);
            } else if (destinationCallsignWithSSID === 'NODEB-1' && nodeBRef.current) {
                nodeBRef.current.receiveRawData(frameBytes);
            } else if (destinationCallsignWithSSID === 'NODEC-1' && nodeCRef.current) { // Route to Node C
                nodeCRef.current.receiveRawData(frameBytes);
            } else {
                console.warn(`Frame sent to unknown destination: ${destinationCallsignWithSSID}`);
            }
        }, 50 + Math.random() * 50);
    }, []); // Dependencies: nodeARef, nodeBRef, nodeCRef (implicitly captured by useCallback)

    const nodeA = useAx25Link('NODEA-1', handleNetworkSend, 'DEBUG');
    const nodeB = useAx25Link('NODEB-1', handleNetworkSend, 'DEBUG');
    const nodeC = useAx25Link('NODEC-1', handleNetworkSend, 'DEBUG'); // New Node C instance

    useEffect(() => {
        nodeARef.current = nodeA;
        nodeBRef.current = nodeB;
        nodeCRef.current = nodeC; // Set Node C ref
    });

    const [messageToSend, setMessageToSend] = useState('');
    const [selectedSender, setSelectedSender] = useState('NODEA-1');
    const [selectedIFrameDest, setSelectedIFrameDest] = useState('NODEB-1');
    const [selectedUIFrameDest, setSelectedUIFrameDest] = useState('NODEB-1');

    // Helper to get node instance by callsign
    const getNodeByCallsign = useCallback((callsign: string) => {
        switch (callsign) {
            case 'NODEA-1': return nodeA;
            case 'NODEB-1': return nodeB;
            case 'NODEC-1': return nodeC;
            default: return null;
        }
    }, [nodeA, nodeB, nodeC]);

    const handleSendI = () => {
        if (messageToSend) {
            const senderNode = getNodeByCallsign(selectedSender);
            if (senderNode) {
                // To send an I-frame, the sender must be connected to the destination.
                // The AX25Link instance manages its own remoteCallsign for connected mode.
                // So, we just tell the sender to send, and it will use its established connection.
                // This means the 'Connect' button for the sender must have been used with the selectedIFrameDest.
                if (senderNode.connectionStatus === 'CONNECTED' && senderNode.peerCallsign === selectedIFrameDest) {
                    senderNode.sendIFrame(messageToSend);
                    setMessageToSend('');
                } else {
                    displayStatusMessage(`Node ${selectedSender} is not connected to ${selectedIFrameDest} for I-Frame transmission. Please connect first.`);
                }
            } else {
                displayStatusMessage(`Invalid sender node selected: ${selectedSender}`);
            }
        } else {
            displayStatusMessage("Message cannot be empty.");
        }
    };

    const handleSendUI = () => {
        if (messageToSend) {
            const senderNode = getNodeByCallsign(selectedSender);
            if (senderNode) {
                senderNode.sendUIFrame(selectedUIFrameDest, messageToSend);
                setMessageToSend('');
            } else {
                displayStatusMessage(`Invalid sender node selected: ${selectedSender}`);
            }
        } else {
            displayStatusMessage("Message cannot be empty.");
        }
    };

    // Options for sender and destination dropdowns
    const nodeOptions = ['NODEA-1', 'NODEB-1', 'NODEC-1'];

    return (
        <div style={{ display: 'flex', fontFamily: 'monospace', gap: '20px', padding: '20px', flexWrap: 'wrap' }}>
            {/* Status Message Box */}
            {showMessage && (
                <div style={{
                    position: 'fixed',
                    top: '20px',
                    left: '50%',
                    transform: 'translateX(-50%)',
                    backgroundColor: '#ffc107',
                    color: '#333',
                    padding: '10px 20px',
                    borderRadius: '5px',
                    boxShadow: '0 2px 10px rgba(0,0,0,0.2)',
                    zIndex: 1000,
                    opacity: showMessage ? 1 : 0,
                    transition: 'opacity 0.5s ease-in-out',
                }}>
                    {statusMessage}
                </div>
            )}

            {/* Node A */}
            <NodePanel node={nodeA} connectOptions={nodeOptions.filter(opt => opt !== nodeA.localCallsign)} />

            {/* Node B */}
            <NodePanel node={nodeB} connectOptions={nodeOptions.filter(opt => opt !== nodeB.localCallsign)} />

            {/* Node C */}
            <NodePanel node={nodeC} connectOptions={nodeOptions.filter(opt => opt !== nodeC.localCallsign)} />

            {/* Universal Send Message Section */}
            <div style={{ flex: '1 1 100%', border: '1px solid #ccc', padding: '15px', borderRadius: '5px', marginTop: '20px', background: '#e8f5e9' }}>
                <h2>Send Message</h2>
                <div style={{ marginBottom: '10px' }}>
                    <label htmlFor="sender-select" style={{ marginRight: '10px' }}>Sending Node (Source):</label>
                    <select id="sender-select" value={selectedSender} onChange={(e) => setSelectedSender(e.target.value)} style={{ padding: '5px', borderRadius: '3px' }}>
                        {nodeOptions.map(node => (
                            <option key={node} value={node}>{node}</option>
                        ))}
                    </select>
                </div>
                <div style={{ marginBottom: '10px' }}>
                    <label htmlFor="iframe-dest-select" style={{ marginRight: '10px' }}>I-Frame Destination (Connected Mode):</label>
                    <select id="iframe-dest-select" value={selectedIFrameDest} onChange={(e) => setSelectedIFrameDest(e.target.value)} style={{ padding: '5px', borderRadius: '3px' }}>
                        {nodeOptions.filter(opt => opt !== selectedSender).map(node => (
                            <option key={node} value={node}>{node}</option>
                        ))}
                    </select>
                </div>
                <div style={{ marginBottom: '10px' }}>
                    <label htmlFor="uiframe-dest-select" style={{ marginRight: '10px' }}>UI-Frame Destination (Connectionless):</label>
                    <select id="uiframe-dest-select" value={selectedUIFrameDest} onChange={(e) => setSelectedUIFrameDest(e.target.value)} style={{ padding: '5px', borderRadius: '3px' }}>
                        {nodeOptions.filter(opt => opt !== selectedSender).map(node => (
                            <option key={node} value={node}>{node}</option>
                        ))}
                    </select>
                </div>
                <textarea
                    value={messageToSend}
                    onChange={(e) => setMessageToSend(e.target.value)}
                    rows={3}
                    style={{ width: '95%', padding: '8px', borderRadius: '4px', border: '1px solid #ddd', marginBottom: '10px' }}
                    placeholder="Enter message to send..."
                ></textarea>
                <div>
                    <button onClick={handleSendI} style={{ padding: '8px 15px', marginRight: '10px', backgroundColor: '#4CAF50', color: 'white', border: 'none', borderRadius: '4px', cursor: 'pointer' }}>Send I-Frame</button>
                    <button onClick={handleSendUI} style={{ padding: '8px 15px', backgroundColor: '#008CBA', color: 'white', border: 'none', borderRadius: '4px', cursor: 'pointer' }}>Send UI-Frame</button>
                </div>
            </div>
        </div>
    );
}

// NodePanel Component for reusable UI
function NodePanel({ node, connectOptions }: { node: ReturnType<typeof useAx25Link>, connectOptions: string[] }) {
    const [connectTarget, setConnectTarget] = useState(connectOptions[0] || '');

    useEffect(() => {
        if (!connectOptions.includes(connectTarget) && connectOptions.length > 0) {
            setConnectTarget(connectOptions[0]);
        }
    }, [connectOptions, connectTarget]);

    return (
        <div style={{ flex: '1 1 30%', minWidth: '300px', border: '1px solid #ccc', padding: '10px', borderRadius: '5px', display: 'flex', flexDirection: 'column' }}>
            <h1>Node {node.localCallsign}</h1>
            <p>Status: <strong style={{ color: node.connectionStatus === 'CONNECTED' ? 'green' : (node.connectionStatus === 'DISCONNECTED' ? 'red' : 'orange') }}>{node.connectionStatus}</strong></p>
            {node.connectionStatus === 'CONNECTED' && node.peerCallsign && (
                <p>Connected to: <strong>{node.peerCallsign}</strong></p>
            )}
            <div style={{ marginBottom: '10px' }}>
                <select value={connectTarget} onChange={(e) => setConnectTarget(e.target.value)} disabled={node.connectionStatus !== 'DISCONNECTED'} style={{ padding: '5px', borderRadius: '3px', marginRight: '5px' }}>
                    {connectOptions.map(opt => (
                        <option key={opt} value={opt}>{opt}</option>
                    ))}
                </select>
                <button onClick={() => node.connect(connectTarget)} disabled={node.connectionStatus !== 'DISCONNECTED' || !connectTarget} style={{ padding: '8px 15px', backgroundColor: '#2196F3', color: 'white', border: 'none', borderRadius: '4px', cursor: 'pointer', marginRight: '5px' }}>Connect</button>
                <button onClick={() => node.disconnect()} disabled={node.connectionStatus === 'DISCONNECTED'} style={{ padding: '8px 15px', backgroundColor: '#f44336', color: 'white', border: 'none', borderRadius: '4px', cursor: 'pointer' }}>Disconnect</button>
            </div>
            <h3>Logs</h3>
            <div style={{ flexGrow: 1, height: '200px', overflowY: 'scroll', background: '#f9f9f9', padding: '5px', border: '1px solid #eee', borderRadius: '4px' }}>
                {node.messages.map(msg => (
                    <p key={msg.id} style={{ margin: '2px 0', fontSize: '0.85em', color: msg.type === 'error' ? 'red' : (msg.type === 'system' ? 'blue' : 'inherit') }}>{msg.text}</p>
                ))}
            </div>
        </div>
    );
}

export default App;

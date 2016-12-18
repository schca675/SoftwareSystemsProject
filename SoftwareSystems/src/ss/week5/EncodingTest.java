package ss.week5;

import org.apache.commons.codec.DecoderException;
import org.apache.commons.codec.binary.Hex;

/**
 * A simple class that experiments with the Hex encoding
 * of the Apache Commons Codec library.
 *
 */
public class EncodingTest {
    public static void main(String[] args) throws DecoderException {
        String input = "Hello World";
        String input2 = "Hello Big World";
        String hexString = "4d6f64756c652032";
        char[] hexChars = hexString.toCharArray();
        byte[] hexdecode = Hex.decodeHex(hexChars);
        String hexStringagain = new String(hexdecode);
        
        System.out.println(Hex.encodeHexString(input.getBytes()));
        System.out.println(Hex.encodeHexString(input2.getBytes()));
        System.out.println(hexStringagain);
    }
}

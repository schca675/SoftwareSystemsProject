package ss.week5;

import org.apache.commons.codec.DecoderException;
import org.apache.commons.codec.binary.Base64;
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
        
        // Decode hex string
        String hexString = "4d6f64756c652032";
        char[] hexChars = hexString.toCharArray();
        byte[] hexdecode = Hex.decodeHex(hexChars);
        String hexStringagain = new String(hexdecode);
        
        System.out.println(Hex.encodeHexString(input.getBytes()));
        System.out.println(Hex.encodeHexString(input2.getBytes()));
        System.out.println(hexStringagain);
        
        System.out.println(Base64.encodeBase64String(input.getBytes()));
        
        //String hexString2 = "010203040506";
        char[] hexChars2 = hexString.toCharArray();
        byte[] hexDecode2 = Hex.decodeHex(hexChars2);
        System.out.println(Base64.encodeBase64String(hexDecode2));
        
        // 8 characters long. It's shorter. Fancy.
        
        String base64String = "U29mdHdhcmUgU3lzdGVtcw==";
        System.out.println(new String(Base64.decodeBase64(base64String)));
        
        String stringy = "";
        for (int i = 0; i < 20; i++) {
        	stringy = stringy + "a";
        	System.out.println(Base64.encodeBase64String(stringy.getBytes()) + " : " + stringy);
        }
        
        // Each group of 3 characters is always represented in the same way. 
        // Only the tail of the output changes; when there is no entire group of three characters.
    }
}

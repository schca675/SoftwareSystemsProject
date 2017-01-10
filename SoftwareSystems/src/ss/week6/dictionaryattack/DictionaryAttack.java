package ss.week6.dictionaryattack;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.HashMap;
import java.util.Map;

import org.apache.commons.codec.binary.Hex;


public class DictionaryAttack {
	private Map<String, String> passwordMap;
	private Map<String, String> hashDictionary;

	public DictionaryAttack() {
		passwordMap = new HashMap<String, String>();
		hashDictionary = new HashMap<String, String>();
	}
	/**
	 * Reads a password file. Each line of the password file has the form:
	 * username: encodedpassword
	 * 
	 * After calling this method, the passwordMap class variable should be
	 * filled withthe content of the file. The key for the map should be
	 * the username, and the password hash should be the content.
	 * @param filename
	 */
	public void readPasswords(String filename) throws IOException {
		System.out.println("Reader");
		BufferedReader reader;
		try {
			reader = new BufferedReader(new FileReader(filename));
			String line;
			while ((line = reader.readLine()) != null) {
				String[] parts = line.split(": ");
				if (parts.length == 2) {
					passwordMap.put(parts[0], parts[1]);
				}
			}
			reader.close();
		} catch (IndexOutOfBoundsException e) {
			throw new IOException(e);
		}
		
	}

	/**
	 * Given a password, return the MD5 hash of a password. The resulting
	 * hash (or sometimes called digest) should be hex-encoded in a String.
	 * @param password
	 * @return
	 * @throws NoSuchAlgorithmException 
	 */
	public String getPasswordHash(String password) {
    	try {
    		MessageDigest digester = MessageDigest.getInstance("MD5");
    		return Hex.encodeHexString(digester.digest(password.getBytes()));
    	} catch (NoSuchAlgorithmException e) {
    		return null;
    	}
	}
	/**
	 * Checks the password for the user the password list. If the user
	 * does not exist, returns false.
	 * @param user
	 * @param password
	 * @return whether the password for that user was correct.
	 */
	public boolean checkPassword(String user, String password) {
		if (passwordMap != null) {
			String hashedUserPassword = passwordMap.get(user);
			if (hashedUserPassword != null) {
				return getPasswordHash(password).equals(hashedUserPassword);
			} else {
				return false;
			}
		} else {
			return false;
		}
	}

	/**
	 * Reads a dictionary from file (one line per word) and use it to add
	 * entries to a dictionary that maps password hashes (hex-encoded) to
     * the original password.
	 * @param filename filename of the dictionary.
	 */
    public void addToHashDictionary(String filename) throws IOException {
    	System.out.println("1");
    	BufferedReader reader;
    	try {
    		reader = new BufferedReader(new FileReader(filename));
    		String line;
    		while ((line = reader.readLine()) != null) {
    			hashDictionary.put(getPasswordHash(line), line);
    			System.out.println(getPasswordHash(line) + line);
    		}
    		reader.close();
    	} catch (IndexOutOfBoundsException e) {
    		throw new IOException(e);
    	}      
    }
    
	/**
	 * Do the dictionary attack.
	 */
	public void doDictionaryAttack() {
		for (String username : passwordMap.keySet()) {
			if (hashDictionary.keySet().contains(passwordMap.get(username))) {
				System.out.println(username + hashDictionary.get(passwordMap.get(username)));
			}
		}
	}
}

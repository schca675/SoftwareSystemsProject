package ss.week6.dictionaryattack;

import java.io.IOException;

public class DictionaryAttackPlus {
	
	public static void main(String[] args) throws IOException {
		System.out.println("Hi");
		DictionaryAttack da = new DictionaryAttack();
		da.readPasswords("LeakedPasswords.txt");
		da.addToHashDictionary("CommonPasswords.txt");
		da.doDictionaryAttack();
	}
}

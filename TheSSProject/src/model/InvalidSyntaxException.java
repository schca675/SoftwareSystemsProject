package model;

public class InvalidSyntaxException extends Exception {
	public InvalidSyntaxException(String tested, String type) {
		super("The tested String " + tested + "does not match the protocol type " + type);
	}
}

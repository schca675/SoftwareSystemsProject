package exc;

public class InvalidSyntaxException extends Exception {
	private static final long serialVersionUID = 3L;
	
	/**
	 * Create a new Invalid Syntax Exception.
	 * @param tested message that has a invalid syntax.
	 * @param type Type the message should represent.
	 */
	public InvalidSyntaxException(String tested, String type) {
		super("The tested String " + tested + " does not match the protocol type for " + type);
	}
}

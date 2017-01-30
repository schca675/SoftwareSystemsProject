package exc;

public class InvalidSyntaxException extends Exception {
	private static final long serialVersionUID = 3L;
	public InvalidSyntaxException(String tested, String type) {
		super("The tested String " + tested + " does not match the protocol type for " + type);
	}
}

package ss.week6;

@SuppressWarnings("serial")
public class TooFewArgumentsException extends WrongArgumentException {
	public TooFewArgumentsException(String message, Throwable cause) {
		super(message, cause);
	}
	public TooFewArgumentsException() {
		super("error: must pass two command line arguments"); 
	}
}

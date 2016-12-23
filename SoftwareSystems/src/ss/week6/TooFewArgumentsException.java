package ss.week6;

public class TooFewArgumentsException extends WrongArgumentException {
	public TooFewArgumentsException(String message, Throwable cause) {
		super(message, cause);
	}
	public TooFewArgumentsException() {
		super("error: must pass two command line arguments"); 
	}
}

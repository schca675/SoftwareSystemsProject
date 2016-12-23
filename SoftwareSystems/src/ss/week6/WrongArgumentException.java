package ss.week6;

public class WrongArgumentException extends Exception {
	public WrongArgumentException(String message, Throwable cause) {
		super(message, cause);
	}
	
	public WrongArgumentException(String message) {
		super(message);
	}
	
	public WrongArgumentException() {
		super();
	}

}

package ss.week6;

@SuppressWarnings("serial")
public class ArgumentLengthsDifferException extends WrongArgumentException {
	public ArgumentLengthsDifferException(String message, Throwable cause) {
		super(message, cause);
	}
	
	public ArgumentLengthsDifferException(int length1, int length2) {
		super("error: length of command line arguments " + "differs (" 
				+ length1 + ", " + length2 + ")");
	}

}

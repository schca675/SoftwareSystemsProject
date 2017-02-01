package exc;

public class IllegalBoardConstructorArgumentsException extends Exception {
	private static final long serialVersionUID = 1L;
	
	/**
	 * Returns the message of the exception.
	 * @return String containing the message of the exception.
	 */
	@Override
	public String getMessage() {
		return "Invalid arguments for the board constructor";
	}
	
}
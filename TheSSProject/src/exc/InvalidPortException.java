package exc;

public class InvalidPortException extends Exception {
	private static final long serialVersionUID = 2L;
	private int port;
	
	/**
	 * Constructs a new Invalid Port Exception.
	 * @param port invalid port number.
	 */
	public InvalidPortException(int port) {
		super();
		this.port = port;
	}
	
	/**
	 * Returns the message of the exception.
	 * @return String containing the message of the exception.
	 */
	@Override
	public String getMessage() {
		return "Invalid port number: " + port;
	}
}

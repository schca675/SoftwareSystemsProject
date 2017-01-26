package exc;

public class InvalidPortException extends Exception {
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
	 * Returns a description of the exception.
	 */
	@Override
	public String getMessage() {
		return "Invalid port number: " + port;
	}
}

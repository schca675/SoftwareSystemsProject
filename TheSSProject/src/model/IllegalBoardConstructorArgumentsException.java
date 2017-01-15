package model;

public class IllegalBoardConstructorArgumentsException extends Exception {
	private static final long serialVersionUID = 1L;
	
	@Override
	public String getMessage() {
		return "Invalid arguments for the board constructor";
	}
	
}
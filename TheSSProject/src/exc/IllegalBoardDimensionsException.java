package exc;

import model.Board;

public class IllegalBoardDimensionsException extends IllegalBoardConstructorArgumentsException {
	private static final long serialVersionUID = 1L;
	private int xDim;
	private int yDim;
	private int zDim;
	
	/**
	 * Creates a new IllegalBoard Dimensions Exception.
	 * @param xDim X dimension
	 * @param yDim Y dimension
	 * @param zDim Z dimension
	 */
	public IllegalBoardDimensionsException(int xDim, int yDim, int zDim) {
		this.xDim = xDim;
		this.yDim = yDim;
		this.zDim = zDim;
	}
	
	/**
	 * Returns the message of the exception.
	 * @return String containing the message of the exception.
	 */
	@Override
	public String getMessage() {
		return "Got invalid dimensions for constructing a board. They must be positive, except " + 
				Board.UNLIMITED_Z + " indicating infinite zDim. Got (" + xDim + ", " + yDim +
				", " + zDim + ")";
	}
}

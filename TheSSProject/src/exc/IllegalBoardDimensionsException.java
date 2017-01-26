package exc;

import model.Board;

public class IllegalBoardDimensionsException extends IllegalBoardConstructorArgumentsException {
	private static final long serialVersionUID = 1L;
	private int xDim;
	private int yDim;
	private int zDim;
	
	public IllegalBoardDimensionsException(int xDim, int yDim, int zDim) {
		this.xDim = xDim;
		this.yDim = yDim;
		this.zDim = zDim;
	}
	
	@Override
	public String getMessage() {
		return "Got invalid dimensions for constructing a board. They must be positive, except " + 
				Board.UNLIMITED_Z + " indicating infinite zDim. Got (" + xDim + ", " + yDim +
				", " + zDim + ")";
	}
}

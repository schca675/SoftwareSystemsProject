package exc;

public class IllegalWinningLengthException extends IllegalBoardConstructorArgumentsException {
	private static final long serialVersionUID = 1L;
	private int xDim;
	private int yDim;
	private int zDim;
	private int winningLength;
	
	/**
	 * Creates a new Illegal Winning Length Exception.
	 * @param xDim X dimension of the board
	 * @param yDim Y dimension of the board
	 * @param zDim Z dimension of the board
	 * @param winningLength invalid winning length
	 */
	public IllegalWinningLengthException(int xDim, int yDim, int zDim, int winningLength) {
		this.xDim = xDim;
		this.yDim = yDim;
		this.zDim = zDim;
		this.winningLength = winningLength;
	}
	
	/**
	 * Returns the message of the exception.
	 * @return String containing the message of the exception.
	 */
	@Override
	public String getMessage() {
		return "Constructor: length required to win is greater than largest board dimension. Got "
				+ "win length " + winningLength + " and dimensions (" + xDim + ", " + yDim + ", " 
				+ zDim + ")";
	}
}

package exc;

public class IllegalWinningLengthException extends IllegalBoardConstructorArgumentsException {
	private static final long serialVersionUID = 1L;
	private int xDim;
	private int yDim;
	private int zDim;
	private int winningLength;
	
	public IllegalWinningLengthException(int xDim, int yDim, int zDim, int winningLength) {
		this.xDim = xDim;
		this.yDim = yDim;
		this.zDim = zDim;
		this.winningLength = winningLength;
	}
	
	@Override
	public String getMessage() {
		return "Constructor: length required to win is greater than largest board dimension. Got "
				+ "win length " + winningLength + " and dimensions (" + xDim + ", " + yDim + ", " 
				+ zDim + ")";
	}
}

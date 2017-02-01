package server;

public class GameRulesStruct {
	public final int xDim;
	public final int yDim;
	public final int zDim;
	public final int winLength;
	
	/**
	 * Creates a new Game Rules Structure.
	 * @param xDim X dimension of the board.
	 * @param yDim Y dimension of the board.
	 * @param zDim Z dimension of the board.
	 * @param winLength winning length of the board.
	 */
	//@ requires xDim >= 0 && yDim >= 0 && zDim >= 0 && winLength >=0;
	public GameRulesStruct(int xDim, int yDim, int zDim, int winLength) {
		this.xDim = xDim;
		this.yDim = yDim;
		this.zDim = zDim;
		this.winLength = winLength;
	}
}

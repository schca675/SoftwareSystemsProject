package server;

public class GameRulesStruct {
	public final int xDim;
	public final int yDim;
	public final int zDim;
	public final int winLength;
	
	public GameRulesStruct(int xDim, int yDim, int zDim, int winLength) {
		this.xDim = xDim;
		this.yDim = yDim;
		this.zDim = zDim;
		this.winLength = winLength;
	}
}

package server;

public class GameRules {
	public final int xDim;
	public final int yDim;
	public final int zDim;
	public final int winLength;
	
	public GameRules(int xDim, int yDim, int zDim, int winLength) {
		this.xDim = xDim;
		this.yDim = yDim;
		this.zDim = zDim;
		this.winLength = winLength;
	}
}

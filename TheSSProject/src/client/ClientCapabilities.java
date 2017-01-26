package client;

public class ClientCapabilities {
	public final int amountOfPlayers;
	public final String playerName;
	public final boolean roomSupport;
	public final int maxXDim;
	public final int maxYDim;
	public final int maxZDim;
	public final int winLength;
	public final boolean chatSupport;
	public final boolean autoRefresh;
	
	public ClientCapabilities(int amountOfPlayers, String playerName, boolean roomSupport, int maxXDim, 
			int maxYDim, int maxZDim, int winLength, boolean chatSupport, boolean autoRefresh) {
		this.amountOfPlayers = amountOfPlayers;
		this.playerName = playerName;
		this.roomSupport = roomSupport;
		this.maxXDim = maxXDim;
		this.maxYDim = maxYDim;
		this.maxZDim = maxZDim;
		this.winLength = winLength;
		this.chatSupport = chatSupport;
		this.autoRefresh = autoRefresh;
	}
}

package server;

public class ClientCapabilitiesStruct {
	public final int amountOfPlayers;
	public final String playerName;
	public final boolean roomSupport;
	public final int maxXDim;
	public final int maxYDim;
	public final int maxZDim;
	public final int winLength;
	public final boolean chatSupport;
	public final boolean autoRefresh;
	
	/**
	 * Creates a new Client Capability Structure.
	 * @param amountOfPlayers maximal amount of players the client wants to play with.
	 * @param playerName name of the client's player.
	 * @param roomSupport if the client has room support or not.
	 * @param maxXDim maximal X dimension the client wants to play with.
	 * @param maxYDim maximal Y dimension the client wants to play with.
	 * @param maxZDim maximal Z dimension the client wants to play with.
	 * @param winLength maximal winning length the client wants to play with.
	 * @param chatSupport if the client has chat support or not.
	 * @param autoRefresh if the client wants autoRefresh or not.
	 */
	/*@ requires amountOfPlayers >= 2 && playerName != null && maxXDim >= 0 
	  @ && maxYDim >= 0 && maxZDim >= 0 && winLength >= 0; */
	public ClientCapabilitiesStruct(int amountOfPlayers, String playerName, boolean roomSupport, 
			int maxXDim, int maxYDim, int maxZDim, int winLength, boolean chatSupport, 
			boolean autoRefresh) {
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

package server;

import java.util.List;

import model.Player;

public class ServerMessages {
	private static final String SPACE = " ";
	private static final String PIPE = "|";
	private static final String COLOUR = "ff0000"; 
	
	/**
	 * Generates a serverCapabilites message String.
	 * @param numPlayers Number of players supported
	 * @param roomSupport Room support available
	 * @param maxXDim Maximum X dimension supported
	 * @param maxYDim Maximum X dimension supported
	 * @param maxZDim Maximum X dimension supported
	 * @param winLength Maximum winLength supported
	 * @param chatSupport Chat support available
	 * @return serverCapabilities message
	 */
	//@ requires numPlayers >= 2 && maxXDim >= 0 && maxYDim >=0 && maxZDim >= 0 && winLength >= 0;
	public static String genCapabilitiesString(int numPlayers, boolean roomSupport, int maxXDim, 
			int maxYDim, int maxZDim, int winLength, boolean chatSupport) {
		return Protocol.Server.SERVERCAPABILITIES + SPACE + numPlayers + SPACE + 
				boolToInt(roomSupport) + SPACE + maxXDim + SPACE + maxYDim + SPACE + 
				maxZDim + SPACE + winLength + SPACE + boolToInt(chatSupport);
	}
	
	/**
	 * Generates an assignID message String.
	 * @param id A player ID
	 * @return assignID message
	 */
	public static String genAssignIDString(int id) {
		return Protocol.Server.ASSIGNID + SPACE + id;
	}
	
	/**
	 * Generates a startGame message String.
	 * @param xDim X dimension of this game's board
	 * @param yDim Y dimension of this game's board
	 * @param zDim Z dimension of this game's board
	 * @param winLength Length required to win
	 * @param players Players in this game
	 * @return startGame message
	 */
	//@ requires xDim >= 0 && yDim >= 0 && zDim >= 0 && winLength >= 0;
	//@ requires players != null & (\forall Player player; players.contains(player); player !=null);
	public static String genStartGameString(int xDim, int yDim, int zDim, int winLength, 
			List<Player> players) {
		String s = Protocol.Server.STARTGAME + SPACE + xDim + PIPE + yDim + PIPE + zDim + PIPE 
				+ winLength;
		for (Player player : players) {
			s = s + SPACE + player.playerID + PIPE + player.name + PIPE + COLOUR;
			//This will give everyone the same colour
		}
		return s;
	}
	
	/**
	 * Generates a turnOfPlayer message String.
	 * @param playerID A player's ID
	 * @return turnOfPlayer message
	 */
	public static String genTurnOfPlayerString(int playerID) {
		return Protocol.Server.TURNOFPLAYER + SPACE + playerID;
	}
	
	/**
	 * Generates a notifyMove message String.
	 * @param playerID ID of player that made the move
	 * @param x X coordinate
	 * @param y Y coordinate
	 * @return notifyMove message
	 */
	public static String genNotifyMoveString(int playerID, int x, int y) {
		//Workaround for added protocol coordinate origin definition
		return Protocol.Server.NOTIFYMOVE + SPACE + playerID + SPACE + (x - 1) + SPACE + (y - 1);
	}
	
	/**
	 * Generates a notifyWin message String.
	 * @param playerID ID of player that won
	 * @return notifyWin message
	 */
	public static String genNotifyWinString(int playerID) {
		return Protocol.Server.NOTIFYEND + SPACE + Protocol.EndID.WIN + SPACE + playerID;
	}
	
	/**
	 * Generates a notifyDraw message String.
	 * @return notifyDraw message
	 */
	public static String genNotifyDrawString() {
		return Protocol.Server.NOTIFYEND + SPACE + Protocol.EndID.DRAW;
	}
	
	/**
	 * Generates a notifyDisconnect message String.
	 * @param playerID Disconnected player's ID
	 * @return notifyDisconnect message
	 */
	public static String genNotifyDisconnectString(int playerID) {
		return Protocol.Server.NOTIFYEND + SPACE + Protocol.EndID.DISCONNECT + SPACE + playerID;
	}
	
	/**
	 * Generates a notifyTimeout message String.
	 * @param playerID Timed out player's ID
	 * @return notifyTimeout message
	 */
	public static String genNotifyTimeoutString(int playerID) {
		return Protocol.Server.NOTIFYEND + SPACE + Protocol.EndID.DISCONNECT_THIS + SPACE + 
				playerID;
	}
	
	/**
	 * Generates the error String message when no capabilities are received.
	 * @return error String message
	 */
	public static String genErrorNoCapabilitiesString() {
		return Protocol.Server.ERROR + SPACE + Protocol.ErrorID.NOCAPABILITIES;
	}
	
	/**
	 * Generates the error String message when an invalid Command is received.
	 * @return error String message
	 */
	public static String genErrorInvalidCommandString() {
		return Protocol.Server.ERROR + SPACE + Protocol.ErrorID.INVALIDCOMMAND;
	}
	
	/**
	 * Generates the error String message when an invalid move is received.
	 * @return error String message
	 */
	public static String genErrorInvalidMoveString() {
		return Protocol.Server.ERROR + SPACE + Protocol.ErrorID.INVALIDMOVE;
	}
	
	/**
	 * Generates the error String message when an illegal string is received.
	 * @return error String message
	 */
	public static String genErrorIllegalStringString() {
		return Protocol.Server.ERROR + SPACE + Protocol.ErrorID.ILLEGALSTRING;
	}
	
	/**
	 * Returns the integer corresponding to the boolean according to the protocol.
	 * @param bool The boolean to check.
	 * @return 1 if bool == true, 0 if bool == false
	 */
	public static int boolToInt(boolean bool) {
		return bool ? 1 : 0;
	}

}

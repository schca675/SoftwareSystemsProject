package server;

import java.io.IOException;
import java.util.List;

import model.Player;
import server.Protocol.EndID;
import server.Protocol.ErrorID;
import server.Protocol.Server;

public class ServerMessages {
	private static final String SPACE = " ";
	private static final String PIPE = "|";
	private static final String COLOUR = "ff0000"; 
	
	public static String genCapabilitiesString(int numPlayers, boolean roomSupport, int maxXDim, 
			int maxYDim, int maxZDim, int winLength, boolean chatSupport) throws IOException {
		return Protocol.Server.SERVERCAPABILITIES + SPACE + numPlayers + SPACE + 
				boolToInt(roomSupport) + SPACE + maxXDim + SPACE + maxYDim + SPACE + 
				maxZDim + SPACE + boolToInt(chatSupport);
	}
	
	public static String genStartGameString(int xDim, int yDim, int zDim, int winLength, 
			List<Player> players) {
		String s = Protocol.Server.STARTGAME + SPACE + xDim + SPACE + yDim + SPACE + zDim;
		for (Player player : players) {
			s = s + SPACE + player.playerID + PIPE + player.name + PIPE + COLOUR;
			//This will give everyone the same colour #EVIL
		}
		return s;
	}
	
	public static String genTurnOfPlayerString(int playerID) {
		return Protocol.Server.TURNOFPLAYER + SPACE + playerID;
	}
	
	public static String genNotifyMoveString(int playerID, int x, int y) {
		return Protocol.Server.NOTIFYMOVE + SPACE + playerID + SPACE + x + SPACE + y;
	}
	
	public static String genNotifyWinString(int playerID) {
		return Protocol.Server.NOTIFYEND + SPACE + Protocol.EndID.WIN + SPACE + playerID;
	}
	
	public static String genNotifyDrawString() {
		return Protocol.Server.NOTIFYEND + SPACE + Protocol.EndID.DRAW;
	}
	
	public static String genNotifyDisconnectString(int playerID) {
		return Protocol.Server.NOTIFYEND + SPACE + Protocol.EndID.DISCONNECT + SPACE + playerID;
	}
	
	public static String genNotifyDisconnectThisString(int playerID) {
		return Protocol.Server.NOTIFYEND + SPACE + Protocol.EndID.DISCONNECT_THIS + SPACE + 
				playerID;
	}
	
	public static String genErrorNoCapabilitiesString() {
		return Protocol.Server.ERROR + SPACE + Protocol.ErrorID.NOCAPABILITIES;
	}
	
	public static String genErrorInvalidCommandString() {
		return Protocol.Server.ERROR + SPACE + Protocol.ErrorID.INVALIDCOMMAND;
	}
	
	public static String genErrorInvalidMoveString() {
		return Protocol.Server.ERROR + SPACE + Protocol.ErrorID.INVALIDMOVE;
	}
	
	public static String genErrorIllegalStringString() {
		return Protocol.Server.ERROR + SPACE + Protocol.ErrorID.ILLEGALSTRING;
	}
	
	private static int boolToInt(boolean bool) {
		return bool ? 1 : 0;
	}

}

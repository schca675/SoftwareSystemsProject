package controller;

import java.net.ServerSocket;
import java.net.Socket;
import java.util.List;
import java.util.Map;
import java.util.Observable;
import java.util.Observer;

import model.Player;

public class Server {
	public class PlayerIDProvider implements Observer {
		private List<Integer> usedIDs;
		
		public PlayerIDProvider() {
			
		}
		
		/**
		 * Returns the lowest unused integer ID.
		 * @return Unused player ID
		 */
		public int getNewID() {
			return 0;
		}
		
		/** 
		 * Gets notified when an ID of a player can be removed.
		 */
		@Override
		public void update(Observable thingy, Object id) {
			
		}
	}
	
	private List<Player> lobbyPlayerList;
	private Map<Player, Socket> playerMap;
	private PlayerIDProvider playerIDProvider;
	private ServerSocket serverSocket;
	
	/** 
	 * Main method to launch the server.
	 * @param args
	 */
	public static void main(String[] args) {
		int port;
		boolean enableExtensions;
		
		if (args.length == 2 && (args[1].equals("true") || args[1].equals("false"))) {
			try {
				port = Integer.parseInt(args[0]);
				enableExtensions = Boolean.parseBoolean(args[1]);
			} catch (NumberFormatException e) {
				System.out.println(USAGE);
			}
		} else {
			System.out.println(USAGE);
		}
		
	}
	
	/**
	 * Starts a new game thread with default rules for the given players. 
	 * First two players in the playerList given to game, socket can be retrieved from the map.
	 * @param players
	 */
	public void startGame(List<Player> players) {
		
	}
	
	/**
	 * Starts a new game thread with specified rules for the given players.
	 * First (two) players in the playerList given to game, socket can be retrieved from the map.
	 */
	public void startGame(List<Player> players, int xDim, int yDim, int zDim, int winLength) {
		
	}
	
	// MAKING CONNECTIONS!!!!!
}

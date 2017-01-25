package controller;

import java.io.IOException;
import java.net.Socket;
import java.util.List;
import java.util.Map;
import java.util.Observable;
import java.util.Observer;

import model.Player;
import view.ServerTUI;

public class Server implements Observer {
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
	
	public static final int EXT_PLAYERS = 2;
	public static final int EXT_DIM = 0;
	public static final int EXT_WINLENGTH = 0;
	
	private int port;
	private boolean enableExtensions;
	private List<Player> lobbyPlayerList;
	private Map<Player, Socket> socketMap;
	private Map<Player, Capabilities> capabilitiesMap;
	private PlayerIDProvider playerIDProvider;
	private static final String USAGE = "";
	private view.ServerTUI view;
	
	public Server(int port, boolean enableExtensions, view.ServerTUI view) throws IOException {
		this.port = port;
		this.enableExtensions = enableExtensions;
		ServerListener listener = new ServerListener(port, view);
		listener.addObserver(this);
		listener.run();
	}
	
	/** 
	 * Main method to launch the server.
	 * @param args
	 */
	public static void main(String[] args) {
		int port;
		boolean enableExtensions;
		
		try {
			if (args.length == 2 && (args[1].equals("true") || args[1].equals("false")) && 
					Integer.parseInt(args[0]) >= 0 && Integer.parseInt(args[0]) <= 65535) {
				port = Integer.parseInt(args[0]);
				enableExtensions = Boolean.parseBoolean(args[1]);
				ServerTUI view = new ServerTUI();
				new Server(port, enableExtensions, view);
			} else {
				System.out.println(USAGE);
			}
		} catch (NumberFormatException e) {
			System.out.println(USAGE);
		} catch (IOException e) {
			System.err.println(e.getMessage());
		}
	}
	
	@Override
	public void update(Observable o, Object arg) {
		// Client connects
		if (arg instanceof Socket) {
			System.out.println("Client with IP " + ((Socket) arg).getInetAddress() + 
					" connected at port " + ((Socket) arg).getPort());
			initConnection((Socket) arg);
		// Message, atm just errors
		} else if (arg instanceof String) {
			System.err.println(o.toString() + arg);
		}
	}
	
	public void initConnection(Socket socket) {
		ServerPeer peer = new ServerPeer(socket, view);
		peer.run();
		if (enableExtensions) {
			peer.sendCapabilities(EXT_PLAYERS, false, EXT_DIM, EXT_DIM, EXT_DIM, EXT_WINLENGTH, false);
		} else {
			peer.sendCapabilities(2, false, 4, 4, 4, 4, false);
		}
	}
	
	public List<Player> matchPlayers() {
		
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

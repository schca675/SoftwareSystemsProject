package server;

import java.io.IOException;
import java.net.Socket;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Observable;
import java.util.Observer;
import java.util.Set;

import client.ClientCapabilities;
import model.Player;

public class Server implements Observer {
	public class PlayerIDProvider {
		private Set<Integer> usedIDs;
		
		public PlayerIDProvider() {
			usedIDs = new HashSet<Integer>();
		}
		
		/**
		 * Returns the lowest unused integer ID.
		 * @return Unused player ID
		 */
		public int obtainID() {
			int id = 0;
			while (true) {
				if (!usedIDs.contains(id)) {
					usedIDs.add(id);
					return id;
				} else {
					id++;
				}
			}
		}
		
		public void releaseID(int id) {
			usedIDs.remove(id);
		}
	}
	
	public static final int EXT_PLAYERS = 2;
	public static final int EXT_DIM = 0;
	public static final int EXT_WINLENGTH = 0;
	public static final boolean EXT_ROOMS = false;
	public static final boolean EXT_CHAT = false;
	
	private int port;
	private boolean enableExtensions;
	private List<Player> lobbyPlayerList;
	private Map<Player, ClientHandler> handlerMap;
	private Map<Player, ClientCapabilities> capabilitiesMap;
	private PlayerIDProvider playerIDProvider;
	private static final String USAGE = "";
	private ServerTUI view;
	
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
		}
	}
	
	/**
	 * Server constructor.
	 * @param port Port to bind the connection listener to
	 * @param enableExtensions Whether to enable extensions (currently larger board, 
	 * winning length supported)
	 * @param view View to use;
	 */
	public Server(int port, boolean enableExtensions, ServerTUI view) {
		this.port = port;
		this.enableExtensions = enableExtensions;
		this.playerIDProvider = new PlayerIDProvider();
		lobbyPlayerList = new ArrayList<Player>(10);
		handlerMap = new HashMap<Player, ClientHandler>(10);
		capabilitiesMap = new HashMap<Player, ClientCapabilities>(10);
		listenForConnections();
	}
	
	/**
	 * Method that initiates listening for incoming connections.
	 */
	public void listenForConnections() {
		ServerListener listener = new ServerListener(port, view);
		listener.addObserver(this);
		new Thread(listener).start();
	}

	/**
	 * Update method, used for handling commands to be executed after a ClientHandler receives a 
	 * valid communication message while in the initial connection stage.
	 * @param o Caller
	 * @param arg Object that was created after receiving a valid message
	 */
	@Override
	public synchronized void update(Observable o, Object arg) {
		// Client connects
		if (arg instanceof Socket) {
			System.out.println("Client with IP " + ((Socket) arg).getInetAddress() + 
					" connected at port " + ((Socket) arg).getPort());
			initConnection((Socket) arg);
		} else if (arg instanceof ClientCapabilities && o instanceof ClientHandler) {
			initPlayer((ClientHandler) o, (ClientCapabilities) arg);
		} else if (arg instanceof String) {
			// Message, atm just errors
			System.err.println(o.toString() + arg);
		} else {
			System.out.println("Invalid call to main server update");
		}
	}
	
	/**
	 * Initiates a connection to the given socket, e.g. starts a handler for this socket and sends 
	 * the initial server message. Starts timeout in handler for handshake from client.
	 * @param socket A socket
	 */
	public void initConnection(Socket socket) {
		//TODO: look at exceptions
		ClientHandler peer = null;
		try {
			peer = new ClientHandler(socket, view);
			new Thread(peer).start();
			if (enableExtensions) {
				peer.sendMessage(ServerMessages.genCapabilitiesString(EXT_PLAYERS, EXT_ROOMS, 
						EXT_DIM, EXT_DIM, EXT_DIM, EXT_WINLENGTH, EXT_CHAT));
			} else {
				peer.sendMessage(ServerMessages.genCapabilitiesString(2, false, 4, 4, 4, 4, false));
			}
			peer.startTimeout();
		} catch (IOException e) { }
	}
	
	/**
	 * Creates a player and stores relevant data (player, handler and capabilities). Calls 
	 * matchplayer to see if the new player would allow a game to be started according to its 
	 * criteria.
	 * @param handler ClientHandler for this player/client
	 * @param caps Capabilities of this player/client
	 */
	public void initPlayer(ClientHandler handler, ClientCapabilities caps) {
		int id = playerIDProvider.obtainID();
		Player player = new Player(caps.playerName, id);
		handler.sendMessage(ServerMessages.genAssignIDString(id));
		lobbyPlayerList.add(player);
		handlerMap.put(player, handler);
		capabilitiesMap.put(player, caps);
		matchPlayers(player);
	}
	
	/**
	 * Checks if the given player would allow a game to be started. Current implementation is very 
	 * basic, just starts a game between the first to players connected.
	 * @param player Player to match
	 */
	public void matchPlayers(Player player) {
		//TODO: implement more sophisticated matching, for the moment just first players.
		List<Player> players = new ArrayList<Player>(2);
		players.add(lobbyPlayerList.get(0));
		players.add(lobbyPlayerList.get(1));
		startGame(players);
	}
	
	/**
	 * Starts a new game thread with default rules for the given players. 
	 * First two players in the playerList given to game, socket can be retrieved from the map.
	 * @param players
	 */
	public void startGame(List<Player> players) {
		
	}
}

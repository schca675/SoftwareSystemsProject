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

import model.Player;
import view.ServerTUI;

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
	public static final int EXT_XYDIM = 0;
	public static final int EXT_ZDIM = 0;
	public static final int EXT_DIM_BOUND = 100;
	public static final int EXT_WINLENGTH = 10;
	public static final boolean EXT_ROOMS = false;
	public static final boolean EXT_CHAT = false;
	
	private int port;
	private boolean enableExtensions;
	private List<Player> lobbyPlayerList;
	private Map<Player, ClientHandler> handlerMap;
	private Map<Player, ClientCapabilitiesStruct> capabilitiesMap;
	private PlayerIDProvider playerIDProvider;
	private ServerTUI view;
	
	/** 
	 * Main method to launch the server.
	 * @param args
	 */
	public static void main(String[] args) {
		ServerTUI ui = new ServerTUI();
		int port = ui.requestPortNumber();
		boolean enableExtensions = ui.requestExtensions();
		ui.printMessage("Starting server bound at port " + port + 
				(enableExtensions ? " with " : " without ") + "extensions...");
		try {
			Server server = new Server(port, enableExtensions, ui);
			server.listenForConnections();
		} catch (IOException e) {
			ui.printMessage("Port in use, please enter another one");
			port = ui.requestPortNumber();
			try {
				new Server(port, enableExtensions, ui);
			} catch (IOException exc) {
				ui.printMessage("Port also in use, please think before entering something");
			}
		}
	}
	
	/**
	 * Server constructor.
	 * @param port Port to bind the connection listener to
	 * @param enableExtensions Whether to enable extensions (currently larger board, 
	 * winning length supported)
	 * @param view View to use
	 */
	public Server(int port, boolean enableExtensions, ServerTUI view) throws IOException {
		this.port = port;
		this.enableExtensions = enableExtensions;
		this.playerIDProvider = new PlayerIDProvider();
		this.view = view;
		lobbyPlayerList = new ArrayList<Player>(10);
		handlerMap = new HashMap<Player, ClientHandler>(10);
		capabilitiesMap = new HashMap<Player, ClientCapabilitiesStruct>(10);
//		listenForConnections();
//		view.printMessage("Server started");
	}
	
	/**
	 * Method that initiates listening for incoming connections.
	 */
	public void listenForConnections() throws IOException {
		view.printMessage("Server started");
		ConnectionListener listener = new ConnectionListener(port, view, this);
		new Thread(listener).start();
	}
	
	/**
	 * Initiates a connection to the given socket, e.g. starts a handler for this socket and sends 
	 * the initial server message. Starts timeout in handler for handshake from client.
	 * @param socket A socket
	 */
	public void initConnection(Socket socket) {
		ClientHandler peer = null;
		peer = new ClientHandler(socket, view);
		peer.addObserver(this);
		new Thread(peer).start();
		if (enableExtensions) {
			peer.sendMessage(ServerMessages.genCapabilitiesString(EXT_PLAYERS, EXT_ROOMS, 
					EXT_XYDIM, EXT_XYDIM, EXT_ZDIM, EXT_WINLENGTH, EXT_CHAT));
		} else {
			peer.sendMessage(ServerMessages.genCapabilitiesString(2, false, 4, 4, 4, 4, false));
		}
	}
	
	/**
	 * Update method used by the ClientHandler to indicate a client has responded with its 
	 * capabilities and it is useful to add this information to the server. Only does this 
	 * when the client concerned is not already associated with a created player.
	 */
	public synchronized void update(Observable o, Object arg) {
		if (o instanceof ClientHandler && arg instanceof ClientCapabilitiesStruct) {
			if (!handlerMap.containsValue((ClientHandler) o)) {
				initPlayer((ClientHandler) o, (ClientCapabilitiesStruct) arg);
			} else {
				((ClientHandler) o).bullshitReceived();
			}
		}
	}
	
	/**
	 * Creates a player and stores relevant data (player, handler and capabilities). Calls 
	 * matchplayer to see if the new player would allow a game to be started according to its 
	 * criteria.
	 * @param handler ClientHandler for this player/client
	 * @param caps Capabilities of this player/client
	 */
	private void initPlayer(ClientHandler handler, ClientCapabilitiesStruct caps) {
		synchronized (this) {
			handler.setParentServer(this);
			handler.deleteObserver(this);
			int id = playerIDProvider.obtainID();
			Player player = new Player(caps.playerName, id);
			handler.sendMessage(ServerMessages.genAssignIDString(id));
			lobbyPlayerList.add(player);
			handlerMap.put(player, handler);
			capabilitiesMap.put(player, caps);
			matchPlayers(player);
		}
	}
	
	/**
	 * Checks if the given player would allow a game to be started. Current implementation is very 
	 * basic, just starts a game between the first to players connected.
	 * @param player Player to match
	 */
	private void matchPlayers(Player player) {
		//TODO: implement more sophisticated matching, for the moment just first players.
		//view.printMessage("matchPlayers called");
		if (lobbyPlayerList.size() >= 2) {
			List<Player> players = new ArrayList<Player>(2);
			players.add(lobbyPlayerList.get(0));
			players.add(lobbyPlayerList.get(1));
			startGame(players, determineRules(players));
		}
	}
	
	/**
	 * Determines the lowest common divisor of rules between players and the server.
	 * @param players List of players
	 * @return Most extended rule set supported by all players, server
	 */
	private GameRulesStruct determineRules(List<Player> players) {
		//view.printMessage("determineRules called");
		if (enableExtensions) {
			int xDim = compareDims(Server.EXT_XYDIM, Server.EXT_DIM_BOUND);
			int yDim = compareDims(Server.EXT_XYDIM, Server.EXT_DIM_BOUND);
			int zDim = compareDims(Server.EXT_XYDIM, Server.EXT_DIM_BOUND);
			int winLength = Server.EXT_WINLENGTH;
			for (Player player : players) {
				xDim = compareDims(xDim, capabilitiesMap.get(player).maxXDim);
				yDim = compareDims(yDim, capabilitiesMap.get(player).maxYDim);
				zDim = compareDims(zDim, capabilitiesMap.get(player).maxZDim);
				winLength = compareDims(winLength, capabilitiesMap.get(player).winLength);
			}
			return new GameRulesStruct(xDim, yDim, zDim, winLength);
		} else {
			return new GameRulesStruct(4, 4, 4, 4);
		}
	}
	
	/**
	 * Compares two dimensions, according to the protocol dim==0 stands for infinity.
	 * @param dim1 First dimension
	 * @param dim2 Second dimension
	 * @return 'Greatest' dimension
	 */
	private int compareDims(int dim1, int dim2) {
		if (dim1 == 0 || dim2 == 0) {
			return java.lang.Math.max(dim1, dim2);
		} else {
			return java.lang.Math.min(dim1, dim2);
		}
	}
	
	/**
	 * Starts a new game thread with given rules for the given players. Removes all relevant 
	 * player data from the server and hands it to the GameThread. Updates parent variables for the 
	 * ClientHandlers.
	 * @param players List of players
	 * @param rules Rules for given players, server
	 */
	private void startGame(List<Player> players, GameRulesStruct rules) {
		//view.printMessage("startGame called");
		Map<Player, ClientHandler> handlers = new HashMap<Player, ClientHandler>(players.size());
		for (Player player : players) {
			handlers.put(player, handlerMap.get(player));
			lobbyPlayerList.remove(player);
			handlerMap.remove(player);
			capabilitiesMap.remove(player);
			playerIDProvider.releaseID(player.playerID);
		}
		Game game = new Game(players, handlers, rules, view);
		for (ClientHandler handler : handlers.values()) {
			handler.setParentServer(null);
			handler.setParentGame(game);
		}
		new Thread(game).start();
	}
	
	/** 
	 * Removes all data associated with this ClientHandler's player from this server's variables.
	 * @param client A ClientHandler
	 */
	public synchronized void removeClient(ClientHandler client) {
		synchronized (this) {
			// Game may have been started with this client
			if (handlerMap.containsValue(client)) {
				for (Map.Entry<Player, ClientHandler> handlerMapEntry : handlerMap.entrySet()) {
					if (handlerMapEntry.getValue() == client) {
						lobbyPlayerList.remove(handlerMapEntry.getKey());
						handlerMap.remove(handlerMapEntry.getKey());
						capabilitiesMap.remove(handlerMapEntry.getKey());
						break;
					}
				}
			}
		}
	}
}

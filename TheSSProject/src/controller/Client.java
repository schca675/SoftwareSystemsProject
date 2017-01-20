package controller;

import java.io.IOException;
import java.net.InetAddress;
import java.net.Socket;
import java.net.UnknownHostException;
import java.util.List;
import java.util.Observable;
import java.util.Observer;

import model.Board;
import model.ComputerPlayer;
import model.IllegalCoordinatesException;
import model.InvalidPortException;
import model.Player;
import model.RandomStrategy;
import model.Strategy;
import model.TowerCoordinates;
import view.ClientTUI;

public class Client implements Observer {
	private ClientTUI view;
	
	//needed for the server connection.
	private InetAddress addr;
	private Socket socket;
	private int port;
	
	// needed for the game.
	private Board board;
	private List<Player> players;
	private Player me;
	
	// needed in case the user wants to play as human player.
	private String playerName;
	// needed in case the user wants to play as computer player.
	private Strategy strategy;
	
	// needed in case the client wants to play with own dimensions.
	private int x;
	private int y;
	private int z;
	private int win;
	
	/**
	 * Constructor, empty for now.
	 */
	public Client() {
		view = new ClientTUI(this); 
		board = null;
		playerName = "Initial";
		strategy = null;
		me = null;
		players = null;
		socket = null;
		addr = null;
		port = -1;
		x = Board.DEFAULT_DIM;
		y = Board.DEFAULT_DIM;
		z = Board.DEFAULT_DIM;
		win = Board.DEFAULT_WIN;
	}
	
	//<<--------- Methods to communicate with TUI -------->>
	
	/**
	 * Initialises a game.
	 */
	public void playMenu() {
		//Determine if user is a computer or a human player 
		boolean human = view.determinePlayer();
		if (human) { 
			playerName = view.determinePlayerName();
		} else {
			String typeStrategy = view.determineStrategy();
			switch (typeStrategy) {
				case "Randi":
					strategy = new RandomStrategy();
					break;
				default:
					strategy = new RandomStrategy();
			}
		}
		
		//Determine if user wants to play with default or own dimensions 
		// and communicates it to the client controller.
		boolean defaultDim = view.determineDimensions();
		if (defaultDim) {
			x = Board.DEFAULT_DIM;
			y = Board.DEFAULT_DIM;
			z = Board.DEFAULT_DIM;
			win = Board.DEFAULT_WIN;
		} else {
			x = view.getXDimension();
			y = view.getYDimension();
			z = view.getZDimension();
			win = view.getWinDimension();
		}
		view.displayDimensions(x, y, z, win);
		
		//Determine the connection details of the server, the client want to connect to.
		boolean entered = false;
		
		//Check the Internetaddress
		String address = null;
		while (!entered) {
			address = view.getInetAddress();
			try {
				setInetAddress(address);
				entered = true;
			} catch (UnknownHostException e) {
				view.errorMessage(1);
			}
			
		}
		
		//Check the port number.
		entered = false;
		int newPort = -1;
		while (!entered) {
			newPort = view.getPort();
			try {
				setPort(newPort);
				entered = true;
			} catch (InvalidPortException e) {
				view.errorMessage(2);
			}
		}
		connect();
	}
	
	public void terminateMenu() {
		view.terminateMenu();
		shutdown();
	}
	
	//<<---- Methods needed to do the setup --------------->
	
	/**
	 * Determines the Internet Addres to connect to.
	 * @param address Internet Address to connect to.
	 * @throws UnknownHostException Exception if the given Internet Adress is not valid.
	 */
	//TUI catches Exception!!
	public void setInetAddress(String address) throws UnknownHostException {
		this.addr = InetAddress.getByName(address);
	}
	
	/**
	 * Determines the port to connect to.
	 * Only port numbers above 1000 are accepted.
	 * @param port Port to connect to.
	 * @throws InvalidPortException Exception if the given port is not in a valid range.
	 */
	//TUI catches Exception!!
	public void setPort(int newport) throws InvalidPortException {
		if (newport >= 1000 && newport <= 65535) {
			this.port = newport;
		} else {
			throw new InvalidPortException(newport);
		}
	}
	
	/**
	 * Sets the me-player's name in case me is a Human Player.
	 * @param name Name of the me-player
	 */
	public void setPlayerName(String name) {
		playerName = name;
	}
	
	/**
	 * Sets the me-player's strategy in case  me is a Computer Player.
	 * @param name name of the strategy.
	 */
	public void setStrategy(String name) {
		switch (name) {
			case "Randi":
				strategy = new RandomStrategy();
				break;
			default:
				strategy = new RandomStrategy();
		}
	}
	
	// <--------- Connection methods --------->>
	/**
	 * Reads a server message from the socket, and calls appropriate methods.
	 */
	public void readServerMessage() {
		
	}
	
	/**
	 * Sends a message to the server via the socket.
	 * @param message
	 */
	public void sendServerMessage(String message) {
		
	}
	

	/**
	 * Connecting to server.
	 * If the connection fails, the TUI gets informed and the client resets.
	 */
	public void connect() {
		//Socket and Port and IPaddress in the TUI.
		if (!(addr == null) && port >= 0 && port <= 65535) {
			//Check the IP address
			try {
				socket = new Socket(addr, port);
				view.valid(1);
			} catch (IOException e) {
				view.errorMessage(5);
				reset(); 
			}
			
		}
		
	}
	
	/** 
	 * Disconnects from the server.
	 */
	private void disconnect() {
		try {
			socket.close();
		} catch (IOException e) {
			view.errorMessage(3);
		}
	}
	
	// <<---- Game related methods ---------->>
	/**
	 * Makes the connection to server, calls readTUIMessage(), if rules are fine setup game, 
	 * else notify TUI.
	 * @param message
	 */
	public void startGame() {
		if (me != null && players != null && board != null) {
			//TODO
		}
	}
	

	
	/** 
	 * Makes the moves on the board, handles boards exception after getting the coordinates from 
	 * the server.
	 * @param x X Coordinate of the Tower, the player is playing.
	 * @param y Y Coordinate of the Tower, the player is playing.
	 * @param id ID of the player whose move it is.
	 */
	public void makeMove(int newX, int newY, int newID) {
		try {
			board.makeMove(newX, newY, newID);
		} catch (IllegalCoordinatesException e) {
			disconnect();
		}
	}
	
	/** 
	 * Determines the next move to play, asks TUI in case of Human Player or the method of Computer
	 * Player, handles exceptions before server communication (local check).
	 * @return the TowerCoordinates the me-Player wants to play.
	 */
	public TowerCoordinates determineMove() {
		if (me != null) {
			if (me instanceof ComputerPlayer) {
				return ((ComputerPlayer) me).determineMove(board);
			} else {
				boolean valid = false;
				TowerCoordinates coord = new TowerCoordinates(-1, -1);
				while (!valid) {
					coord = view.determineMove(); 
					if (coord != null && board.isValidMove(coord.getX(), coord.getY())) {
						valid = true;
					} else {
						view.errorMessage(4);
					} 
				}
				return coord;
			}
		} else {
			return null;
		}
	}
	
	public TowerCoordinates determineHint() {
		return null;	
	}
	
	/** 
	 * Gets the board data from the board for use by the UI.
	 * @return
	 */

// <<--------- Start/End of application ----------->>
	/**
	 * Starts the TUI, so starts the communication with the user.
	 */
	public void start() {
		view.start();
	}
	
	public void reset() {
		view = new ClientTUI(this); 
		board = null;
		playerName = "Initial";
		strategy = null;
		me = null;
		players = null;
		socket = null;
		addr = null;
		port = -1;
		x = Board.DEFAULT_DIM;
		y = Board.DEFAULT_DIM;
		z = Board.DEFAULT_DIM;
		win = Board.DEFAULT_WIN;
	}

	/**
	 * Creates a new TUI and starts it.
	 * @param args
	 */
	public static void main(String[] args) {
		Client client = new Client();
		client.start();
	}
	
	/**
	 * Terminates the application.
	 */
	public void shutdown() {
		//TODO
	}

// << --------- Observer pattern ------------>>
	/**
	 * After a change is made on the board, the client will alert the TUI 
	 * to print the changed situation.
	 * @param observable Board to observe.
	 * @param type Type of change the board has made.
	 */
	@Override
	public void update(Observable observable, Object type) {
		if (observable instanceof Board && type instanceof Integer) {
			Board playboard = (Board) observable;
			int id = 1;
				id = players.size();
			}
			view.printBoard(playboard.deepDataCopy(), playboard.xDim, 
					playboard.yDim, playboard.zDim, id);
		}
	}
}

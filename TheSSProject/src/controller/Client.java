package controller;

import java.net.InetAddress;
import java.net.Socket;
import java.util.ArrayList;
import java.util.List;
import java.util.Observable;

import model.Board;
import model.IllegalCoordinatesException;
import model.Player;
import model.RandomStrategy;
import model.Strategy;
import model.TowerCoordinates;
import view.ClientTUI;

public class Client extends Observable {
	//Observable if not implemented in Board
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
		players = new ArrayList<Player>();
		socket = null;
		addr = null;
		port = -1;
		x = Board.DEFAULT_DIM;
		y = Board.DEFAULT_DIM;
		z = Board.DEFAULT_DIM;
		win = Board.DEFAULT_WIN;
	}
	/**
	 * Connecting to server.
	 */
	public void connect() {
		if (!(addr == null) && !(socket == null) && port >= 0 && port <= 65535) {
			//Check the IP address
//			try {
//				addr = InetAddress.getByName(addr);
//			}
		}
		
	}
	
	//<<---- Methods needed by the TUI --------------->
	
	
	public void setPlayerName(String name) {
		playerName = name;
	}
	
	public void setStrategy(String name) {
		switch (name) {
			case "Randi":
				strategy = new RandomStrategy();
				break;
			default:
				strategy = new RandomStrategy();
		}
	}
	
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
	 * Makes the connection to server, calls readTUIMessage(), if rules are fine setup game, 
	 * else notify TUI.
	 * @param message
	 */
	public void startGame(String message) {
		
	}
	
	/**
	 * Reads the message, calls appropriate methods.
	 * @param message
	 */
	public void readTUIMessage(String message) {
		
	}
	
	/** 
	 * Disconnects from the server.
	 */
	private void disconnect() {
		
	}
	
	/** 
	 * Makes the moves on the board, handles boards exception after getting the coordinates from 
	 * the server.
	 * @param x X Coordinate of the Tower, the player is playing.
	 * @param y Y Coordinate of the Tower, the player is playing.
	 * @param id ID of the player whose move it is.
	 */
	public void makeMove(int x, int y, int id) {
		try {
			board.makeMove(x, y, id);
		} catch (IllegalCoordinatesException e) {
			disconnect();
		}
	}
	
	/** 
	 * Determines the next move to play, asks TUI in case of Human Player or the method of Computer
	 * Player, handles exceptions before server communication (local check).
	 * @param x
	 * @param y
	 * @return
	 */
	public TowerCoordinates determineMove(int x, int y) {
		return null;
	}
	
	/** 
	 * Gets the board data from the board for use by the UI.
	 * @return
	 */

	public List<List<Integer>> getBoardData() {
		return null;
	}
	

	/**
	 * Starts the TUI, so starts the communication with the user.
	 */
	public void start() {
		view.start();
	}

	/**
	 * Creates a new TUI and starts it.
	 * @param args
	 */
	public static void main(String[] args) {
		Client client = new Client();
		client.start();
	}

}

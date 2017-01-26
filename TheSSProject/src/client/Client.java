package client;

import java.io.IOException;
import java.net.InetAddress;
import java.net.Socket;
import java.net.UnknownHostException;
import java.util.List;
import java.util.Observable;
import java.util.Observer;

import exc.IllegalCoordinatesException;
import exc.InvalidPortException;
import exc.TowerCoordinates;
import model.Board;
import model.ComputerPlayer;
import model.Player;
import model.RandomStrategy;
import model.Strategy;
import view.ClientTUI;

public class Client {
	private ClientTUI view;
	
	//needed for the server connection.
	private InetAddress addr;
	private Socket socket;
	private int port;
	private Thread client;
	
	// needed in case the user wants to play as human player.
	private String playerName;
	// needed in case the user wants to play as computer player.
	private Strategy strategy;
	
	// needed in case the client wants to play with own dimensions.
	private int x;
	private int y;
	private int z;
	private int win;
	
	//needed in case the player wants a hint.
	private ComputerPlayer hintGiver;
	private Board board;
	
	/**
	 * Creates a new client.
	 */
	public Client() { 
		view = new ClientTUI(this); 
		playerName = "Initial";
		strategy = null;
		socket = null;
		addr = null;
		port = -1;
		x = Board.DEFAULT_DIM;
		y = Board.DEFAULT_DIM;
		z = Board.DEFAULT_DIM;
		win = Board.DEFAULT_WIN;
		hintGiver = new ComputerPlayer(-1);
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
	
	/**
	 * Calls the terminate Menu.
	 */
	public void terminateMenu() {
		view.terminateMenu();
		disconnect();
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
			try {
				client = new ClientCommunication(socket, view, playerName, this);
				client.start();
				try {
					client.join();
				} catch (InterruptedException e) {
					//do nothing
				}
				
			} catch (IOException e) {
				view.errorMessage(8);
				reset(); 
			} finally {
				reset();
			}		
		}
		
	}
	
	/** 
	 * Disconnects from the server.
	 */
	//TODO see if this is needed.
	private void disconnect() {
		try {
			socket.close();
		} catch (IOException e) {
			view.errorMessage(3);
		}
	}
	
	// <<---- Game related methods ---------->>
	
	
	public TowerCoordinates determineMove(Board board) {
		return view.determineMove();
	}
	
	/**
	 * Gives the playing user a hint.
	 * @return the hint of the internal computerplayer.
	 */
	public TowerCoordinates determineHint(Board board) {
		if (board != null) {
			return hintGiver.determineMove(board);
		}
		return new TowerCoordinates(-1, -1);	
	}
	

// <<--------- Start/End of application ----------->>
	/**
	 * Starts the TUI, so starts the communication with the user.
	 */
	public void start() {
		view.start();
	}
	
	public void reset() {
		view.errorMessage(10); 
		playerName = "Initial";
		strategy = null;
		socket = null;
		addr = null;
		port = -1;
		x = Board.DEFAULT_DIM;
		y = Board.DEFAULT_DIM;
		z = Board.DEFAULT_DIM;
		win = Board.DEFAULT_WIN;
		view.startMenu();
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

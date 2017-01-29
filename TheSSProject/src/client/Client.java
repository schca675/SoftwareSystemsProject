package client;

import java.io.IOException;
import java.net.InetAddress;
import java.net.Socket;
import java.net.UnknownHostException;

import exc.InvalidPortException;
import model.Board;
import model.RandomStrategy;
import model.SmartStrategy;
import model.Strategy;
import view.ClientTUI;
import view.MessageType;

public class Client {
	private ClientTUI view;
	
	//needed for the server connection.
	private InetAddress addr;
	private Socket socket;
	private int port;
	//private Thread client;
	//TODO
	
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
	 * Creates a new client.
	 */
	public Client() { 
		view = new ClientTUI(); 
		playerName = "Initial";
		strategy = null;
		socket = null;
		addr = null;
		port = -1;
		x = Board.DEFAULT_DIM;
		y = Board.DEFAULT_DIM;
		z = Board.DEFAULT_DIM;
		win = Board.DEFAULT_WIN;
	}
	
	//<<--------- Methods to communicate with TUI -------->>
	
	public void startMenu() {
		boolean play = false;
		do {
			String input = view.startMenu();
			switch (input) {
				case "Help":
					view.helpMenu();
					break;
				case "Play":
					playMenu();
					play = true;
					break;
				case "Exit":
					play = true;
					terminateMenu();
					break;
				default:
					view.errorMessage(MessageType.INVALID_INPUT);
					break;
			}
		} while (!play);
	}	
	
	/**
	 * Initialises a game.
	 */
	public void playMenu() { 
		//Determine if user is a computer or a human player 
		boolean human = view.determinePlayer();
		if (human) { 
			setPlayerName(view.determinePlayerName());
		} else {
			String typeStrategy = view.determineStrategy();
			setStrategy(typeStrategy);
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
				view.errorMessage(MessageType.INVALID_ADDRESS);
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
				view.errorMessage(MessageType.INVALID_PORT);
			}
		}
		connect();
	}
	
	/**
	 * Calls the terminate Menu.
	 */
	public void terminateMenu() {
		view.terminateMenu();
		//TODO
		//disconnect();
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
			case "Trams":
				strategy = new SmartStrategy();
				break;
			default:
				//theoretically never called.
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
				view.valid(MessageType.SOCKET_CREATED);
				try {
					ClientCommunication thisClient = new ClientCommunication(socket, view, 
							playerName, strategy, this, x, y, z, win);
					view.addObserver(thisClient);
					thisClient.run();
					view.print("New communication thread with server started.");
//					// We do not need concurrency for our project but if one wants to include that
//					// a client can connect to multiple servers, this could be used.
//					client = new Thread(thisClient);
//					client.run();
					//TODO
//					try {
//						client.join();
//					} catch (InterruptedException e) {
//						//do nothing
//					}
					
				} catch (IOException e) {
					view.errorMessage(MessageType.STREAM_FAILURE);
					reset(); 
				} finally {
					reset();
				}	
			} catch (IOException e) {
				view.errorMessage(MessageType.SOCKET_FAILURE);
				reset(); 
			}
		}
		
	}
	
	/** 
	 * Disconnects from the server.
	 */
	//TODO see if this is needed.
//	private void disconnect() {
//		try {
//			socket.close();
//		} catch (IOException e) {
//			view.errorMessage(MessageType.PROBLEM_DISCONNECTING);
//		}
//	}
	
// <<--------- Start/End of application ----------->>
	/**
	 * Starts the TUI, so starts the communication with the user.
	 */
	public void start() {
		view.start();
		this.startMenu();
	}
	
	public void reset() {
		view.errorMessage(MessageType.RETURN_START); 
		playerName = "Initial";
		strategy = null;
		socket = null;
		addr = null;
		port = -1;
		x = Board.DEFAULT_DIM;
		y = Board.DEFAULT_DIM;
		z = Board.DEFAULT_DIM;
		win = Board.DEFAULT_WIN;
		startMenu();
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

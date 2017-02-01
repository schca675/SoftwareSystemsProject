package server;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;
import java.util.Observable;

import model.TowerCoordinates;
import view.ServerTUI;

public class ClientHandler extends Observable implements Runnable {
	private Socket socket;
	private BufferedReader in;
	private BufferedWriter out;
	private int bullshit = 0;
	private static final int BULLSHIT_THRESHOLD = 3;
	private static final String SHUTDOWN_ERROR = "IOException while trying to shut down "
			+ "communication thread with ";
	
	private boolean exit = false;
	private Server server;
	private Game game;
	private ServerTUI view;
	
	/**
	 * Creates a ClientHandler for given socket.
	 * @param socket Socket of a client
	 * @param view View to print communication messages on
	 */
	//@ requires socket !=null && view != null;
	public ClientHandler(Socket socket, ServerTUI view) {
		this.socket = socket;
		this.view = view;
		try {
			in = new BufferedReader(new InputStreamReader(socket.getInputStream()));
			out = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream()));
		} catch (IOException e) {
			view.printMessage("IOException while creating communication channel to " + toString() 
				+ ", trying to shut down");
			shutdown();
		}
	}
	
	/**
	 * Sets the Server field to this server, so handleDisconnect() can notify the server. 
	 * Supposed to be set to null when a game takes over.
	 * @param serverToSet the Server the instance should notify.
	 */
	//@ requires serverToSet == null || serverToSet != null;
	public void setParentServer(Server serverToSet) {
		server = serverToSet;
	}
	
	/**
	 * Sets the Game field to this server, so handleDisconnect() can notify the game. 
	 * Supposed to be set to null until a game takes over.
	 * @param gameToSet A Game the instance should notify.
	 */
	//@requires gameToSet !=null;
	public void setParentGame(Game gameToSet) {
		game = gameToSet;
	}
	
	/**
	 * Send a message to the client connected through this handler's socket.
	 * @param message The message to send.
	 */
	//@ requires message != null;
	public synchronized void sendMessage(String message) {
		try {
			out.write(message);
			out.newLine();
			out.flush();
			printSentMessage(message);
		} catch (IOException e) {
			view.printMessage("IOException while sending '" + message + "' to " + 
					toString());
			handleDisconnect();
		}
	}
	
	/**
	 * Run method for listening in a separate thread.
	 */
	public void run() {
		while (!exit) {
			try {
				//TODO: timeout when line not terminated?
				//TODO: timeout when no response when it is desired?
				// Apparently BufferedReader.readline() throws no IOException if the client closes 
				// the socket, but returns null. Without checking for this, this results in an 
				// infinite loop.
				String message = in.readLine();
				if (message != null) {
					printReceivedMessage(message);
					handleMessage(message);
				} else {
					handleDisconnect();
				}
			} catch (IOException e) {
				handleDisconnect();
			}
		}
	}
	
	/**
	 * Method to handle a received message. 
	 * SENDCAPABILITES is only processed when the server and game fields are not set, i.e. when 
	 * this client has no player associated with it on the Server and is not part of a game.
	 * MAKEMOVE is only processed if a game has been started with this client and the game expects
	 * input from this client.
	 * Any invalid messages result in a call to bullshitReceived(). 
	 * @param message The message to handle.
	 */
	//@ requires message != null;
	private void handleMessage(String message) {
		String[] messageParts = message.split(" ");
		if (messageParts.length > 0) {
			String command = messageParts[0];
			switch (command) {
				case Protocol.Client.SENDCAPABILITIES:
					if (messageParts.length == 10 && server == null && game == null &&
						(messageParts[3].equals("0") || messageParts[3].equals("1")) && 
						(messageParts[8].equals("0") || messageParts[8].equals("1")) && 
						(messageParts[9].equals("0") || messageParts[9].equals("1")) &&
						!messageParts[2].contains("|")) {
						try {
							int numPlayers = Integer.parseInt(messageParts[1]);
							String playerName = messageParts[2];
							boolean roomSupport = argToBool(messageParts[3]);
							int maxXDim = Integer.parseInt(messageParts[4]);
							int maxYDim = Integer.parseInt(messageParts[5]);
							int maxZDim = Integer.parseInt(messageParts[6]);
							int winLength = Integer.parseInt(messageParts[7]);
							boolean chatSupport = argToBool(messageParts[8]);
							boolean autoRefresh = argToBool(messageParts[9]);
							ClientCapabilitiesStruct caps = 
									new ClientCapabilitiesStruct(numPlayers, 
									playerName, roomSupport, maxXDim, maxYDim, maxZDim, 
									winLength, chatSupport, autoRefresh);
							setChanged();
							notifyObservers(caps);
						} catch (NumberFormatException e) {
							bullshitReceived();
							sendMessage(ServerMessages.genErrorIllegalStringString());
						}
					} else if (server != null || game != null) {
						bullshitReceived();
						sendMessage(ServerMessages.genErrorInvalidCommandString());
					} else {
						bullshitReceived();
						sendMessage(ServerMessages.genErrorIllegalStringString());
					}
					break;
				case Protocol.Client.MAKEMOVE:
					if (messageParts.length == 3 && game != null && 
							game.expectsHandlerInput(this)) {
						try {
								//Workaround for added protocol coordinate origin definition
							int x = Integer.parseInt(messageParts[1]) + 1;
							int y = Integer.parseInt(messageParts[2]) + 1;
							TowerCoordinates coords = new TowerCoordinates(x, y);
							synchronized (game) {
								game.processMove(this, coords);
							}
						} catch (NumberFormatException e) {
							sendMessage(ServerMessages.genErrorIllegalStringString());
						}
					} else if (game == null || !game.expectsHandlerInput(this)) {
						bullshitReceived();
						sendMessage(ServerMessages.genErrorInvalidCommandString());
					} else {
						bullshitReceived();
						sendMessage(ServerMessages.genErrorIllegalStringString());
					}
					break;
				default:
					bullshitReceived();
					sendMessage(ServerMessages.genErrorInvalidCommandString());
					break;
			}
		} else {
			bullshitReceived();
			sendMessage(ServerMessages.genErrorInvalidCommandString());
		}
	}
	
	/**
	 * Keeps track of bullshit received. Increases bullshit counter and evaluates if it exceeds 
	 * the threshold, if so, this client is dropped.
	 */
	public synchronized void bullshitReceived() {
		bullshit++;
		if (bullshit >= BULLSHIT_THRESHOLD) {
			handleDisconnect();
		}
	}
	
	/**
	 * Responds to a disconnect or communication failure, shuts down this handler and informs 
	 * parent game or server, if set.
	 */ 
	private void handleDisconnect() {
		view.printMessage(toString() + " disconnected");
		deleteObservers();
		shutdown();
		if (server != null) {
			view.printMessage(toString() + " remove from lobby");
			server.removeClient(this);
		} else if (game != null) {
			view.printMessage(toString() + " replace with computer player");
			game.replaceClient(this);
		}
	}
	
	/** 
	 * Shuts down this handler. This is supposed to happen when everything goes according to plan.
	 */
	public void shutdown() {
		exit = true;
		try {
			out.close();
			in.close();
			socket.close();
		} catch (IOException e) {
			view.printMessage(SHUTDOWN_ERROR + socket.getInetAddress());
		}
	}
	
	/**
	 * Prints a message on the view, with the annotation that it was received and timestamp.
	 * @param message Message the server received and should print to the terminal.
	 */
	//@ requires message != null;
	private void printReceivedMessage(String message) {
		view.printMessage(java.time.LocalTime.now() + " " + toString() + " R " + message);
		
	}
	
	/**
	 * Prints a message on the view, with the annotation that it was send and timestamp.
	 * @param message to print on the terminal.
	 */
	//@ requires message !=null;
	private void printSentMessage(String message) {
		view.printMessage(java.time.LocalTime.now() + " " + toString() + " T " + message);
	}
	
	/**
	 * Provides a textual description of the connection to the client.
	 */
	//@ ensures \result != null;
	@Override
	public String toString() {
		return socket.getInetAddress().getHostAddress() + ":" + socket.getPort();
	}
	
	/**
	 * Checks if a String matched "1", if so return true, else false. Supposed to be called only 
	 * when the String equals "1" or "0".
	 * @param s A String equal to "1" or "0".
	 * @return s.equals("1);
	 */
	//@ requires s.equals("1") || s.equals("0");
	//@ ensures \result == s.equals("1");
	private static boolean argToBool(String s) {
		if (s.equals("1")) {
			return true;
		} else {
			return false;
		}
	}
}

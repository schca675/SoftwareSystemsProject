package server;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;

import model.TowerCoordinates;
import view.ServerTUI;

public class ClientHandler implements Runnable {
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
	
	public ClientHandler(Socket socket, Server server, ServerTUI view) {
		this.socket = socket;
		this.view = view;
		this.server = server;
		try {
			in = new BufferedReader(new InputStreamReader(socket.getInputStream()));
			out = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream()));
		} catch (IOException e) {
			view.printMessage("IOException while creating communication channel to " + toString() 
				+ ", trying to shut down");
			shutdown();
		}
	}
	
	public void setParentServer(Server serverToSet) {
		server = serverToSet;
	}
	
	public void setParentGame(Game gameToSet) {
		game = gameToSet;
	}
	
	// Gets called by both listener thread (run -> handleMessage -> sendMessage) and
	// from observer.update;
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
	
	private void handleMessage(String message) {
		String[] messageParts = message.split(" ");
		if (messageParts.length > 0) {
			String command = messageParts[0];
			switch (command) {
				case Protocol.Client.SENDCAPABILITIES:
					synchronized (server) {
						if (messageParts.length == 10 && server != null &&
							(messageParts[3].equals("0") || messageParts[3].equals("1")) && 
							(messageParts[8].equals("0") || messageParts[8].equals("1")) && 
							(messageParts[9].equals("0") || messageParts[9].equals("1"))) {
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
								ClientCapabilitiesStruct caps = new ClientCapabilitiesStruct(numPlayers, 
										playerName, roomSupport, maxXDim, maxYDim, maxZDim, 
										winLength, chatSupport, autoRefresh);
								server.initPlayer(this, caps);
							} catch (NumberFormatException e) {
								bullshitReceived();
								sendMessage(ServerMessages.genErrorIllegalStringString());
							}
						} else if (server == null) {
							bullshitReceived();
							sendMessage(ServerMessages.genErrorInvalidCommandString());
						} else {
							bullshitReceived();
							sendMessage(ServerMessages.genErrorIllegalStringString());
						}
					}
					break;
				case Protocol.Client.MAKEMOVE:
					synchronized (game) {
						if (messageParts.length == 3 && game != null && 
								game.expectsHandlerInput(this)) {
							try {
								//Workaround for added protocol coordinate origin definition
								int x = Integer.parseInt(messageParts[1]) + 1;
								int y = Integer.parseInt(messageParts[2]) + 1;
								TowerCoordinates coords = new TowerCoordinates(x, y);
								game.processMove(this, coords);
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
	
	public void bullshitReceived() {
		bullshit++;
		if (bullshit >= BULLSHIT_THRESHOLD) {
			handleDisconnect();
		}
	}
	
	private void handleDisconnect() {
		view.printMessage(toString() + " disconnected");
		shutdown();
		if (server != null) {
			view.printMessage(toString() + " remove from lobby");
			server.removeClient(this);
		} else if (game != null) {
			view.printMessage(toString() + " replace with computer player");
			game.replaceClient(this);
		}
	}
	
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
	
	private void printReceivedMessage(String message) {
		view.printMessage(java.time.LocalTime.now() + " " + toString() + " R " + message);
		
	}
	
	private void printSentMessage(String message) {
		view.printMessage(java.time.LocalTime.now() + " " + toString() + " S " + message);
	}
	
	@Override
	public String toString() {
		return socket.getInetAddress().getHostAddress() + ":" + socket.getPort();
	}
	
	private static boolean argToBool(String s) {
		if (s.equals("1")) {
			return true;
		} else {
			return false;
		}
	}
}

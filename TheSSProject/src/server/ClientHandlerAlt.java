package server;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;
import java.net.SocketException;
import java.time.LocalTime;
import java.util.Observable;
import java.util.Scanner;

import model.TowerCoordinates;

public class ClientHandlerAlt extends Observable implements Runnable {
	private Socket socket;
	private InputStreamReader in;
	private BufferedWriter out;
	private int bullshit = 0;
	private static final int BULLSHIT_THRESHOLD = 3;
	private static final String SHUTDOWN_ERROR = "IOException while trying to shut down "
			+ "communication thread with ";
	
	private boolean exit = false;
	private static final int TIMEOUTTHRESHOLDSEC = 5;
	private boolean timeoutRunning = false;
	private LocalTime timeoutStartedTime;
	
	private Server server;
	private GameThread game;
	private ServerTUI view;
	
	public ClientHandlerAlt(Socket socket, Server server, ServerTUI view) throws IOException {
		this.socket = socket;
		this.view = view;
		this.server = server;
		in = new InputStreamReader(socket.getInputStream());
		out = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream()));
	}
	
	public void changeParent(GameThread startingGame) {
		server = null;
		game = startingGame;
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
			setChanged();
			notifyObservers("IOException while sending " + message + " to " + 
					socket.getInetAddress());
			handleDisconnect();
		}
	}
	
	public void run() {
		Scanner inputScanner = new Scanner(in);
		while (!exit) {
			//TODO: timeout when line not terminated?
			//TODO: timeout when no response when it is desired?
			if (!isTimedout()) {
				if (inputScanner.hasNextLine()) {
					String message = inputScanner.nextLine();
					if (message != null) {
						printReceivedMessage(message);
						handleMessage(message);
					}
				}
			} else {
				handleDisconnect();
			}
		}
	}
	
	private boolean isTimedout() {
		if (timeoutRunning && java.time.LocalTime.now().isAfter(timeoutStartedTime.
				plusSeconds(TIMEOUTTHRESHOLDSEC))) {
			view.printMessage("timedout");
			return true;
		} else {
			view.printMessage("nottimedout");
			return false;
		}
	}
	
	private void handleMessage(String message) {
		String[] messageParts = message.split(" ");
		if (messageParts.length > 0) {
			String command = messageParts[0];
			switch (command) {
				case Protocol.Client.SENDCAPABILITIES:
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
							ClientCapabilities caps = new ClientCapabilities(numPlayers, 
									playerName, roomSupport, maxXDim, maxYDim, maxZDim, 
									winLength, chatSupport, autoRefresh);
							stopTimeout();
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
					break;
				case Protocol.Client.MAKEMOVE:
					if (messageParts.length == 3 && game != null && 
						game.expectsHandlerInput(this)) {
						try {
							int x = Integer.parseInt(messageParts[1]);
							int y = Integer.parseInt(messageParts[2]);
							TowerCoordinates coords = new TowerCoordinates(x, y);
							stopTimeout();
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
	
	public void startTimeout() {
		timeoutRunning = true;
		timeoutStartedTime = java.time.LocalTime.now();
	}
	
	private void stopTimeout() {
		timeoutRunning = false;
		timeoutStartedTime = null;
	}
	
	private void handleDisconnect() {
		view.printMessage(toString() + " has disconnected or is being dropped after timeout or "
				+ "repeated illegal messages received");
		shutdown();
		if (server != null) {
			server.removeClient(this);
		} else if (game != null) {
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
	
	public void printReceivedMessage(String message) {
		view.printMessage(java.time.LocalTime.now() + " " + toString() + " R " + message);
		
	}
	
	public void printSentMessage(String message) {
		view.printMessage(java.time.LocalTime.now() + " " + toString() + " S " + message);
	}
	
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

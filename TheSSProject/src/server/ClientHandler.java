package server;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;
import java.time.LocalDateTime;
import java.util.Observable;

import client.ClientCapabilities;
import model.TowerCoordinates;

public class ClientHandler extends Observable implements Runnable {
	private Socket socket;
	private BufferedReader in;
	private BufferedWriter out;
	private ServerTUI view;
	private int bullshit = 0;
	private static final int BULLSHIT_THRESHOLD = 3;
	private static final String SHUTDOWN_ERROR = "IOException while trying to shut down "
			+ "communication thread with ";
	
	private boolean exit = false;
	private boolean wantResponse = false;
	private LocalDateTime timeoutStart;
	private int TIMEOUT_THRESHOLD_SEC = 120;
	
	public ClientHandler(Socket socket, ServerTUI view) throws IOException {
		this.socket = socket;
		this.view = view;
		in = new BufferedReader(new InputStreamReader(socket.getInputStream()));
		out = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream()));
	}
	
	// Gets called by both listener thread (run -> handleMessage -> sendMessage and
	// from observer.update;
	public synchronized void sendMessage(String message) {
		try {
			out.write(message);
			out.newLine();
			out.flush();
			view.printMessage(message);
		} catch (IOException e) {
			view.printMessage("IOException while sending " + message + " to " + 
					socket.getInetAddress());
			shutdown();
		}
	}
	
	public void run() {
		while (!exit) {
			try {
				//TODO: timeout when line not terminated?
				//TODO: timeout when no response when it is desired?
				String message = in.readLine();
				if (message != null) {
					handleMessage(message);
				}
			} catch (IOException e) {
				//TODO: Exception forwarding
				exit = true;
			}
		}
	}
	
	//@ requires message != null;
	public void handleMessage(String message) {
		String[] messageParts = message.split(" ");
		if (messageParts.length > 0) {
			String command = messageParts[0];
			switch (command) {
				case Protocol.Client.SENDCAPABILITIES:
					if (messageParts.length == 10 && 
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
							setChanged();
							notifyObservers(caps);
						} catch (NumberFormatException e) {
							bullshitReceived();
							sendMessage(ServerMessages.genErrorIllegalStringString());
						}
					} else {
						bullshitReceived();
						sendMessage(ServerMessages.genErrorIllegalStringString());
					}
					break;
				case Protocol.Client.MAKEMOVE:
					if (messageParts.length == 3) {
						try {
							int x = Integer.parseInt(messageParts[1]);
							int y = Integer.parseInt(messageParts[2]);
							TowerCoordinates coords = new TowerCoordinates(x, y);
							setChanged();
							notifyObservers(coords);
						} catch (NumberFormatException e) {
							sendMessage(ServerMessages.genErrorIllegalStringString());
						}
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
	
	private void bullshitReceived() {
		bullshit++;
		if (bullshit >= BULLSHIT_THRESHOLD) {
			shutdown();
		}
	}
	
	public void startTimeout() {
		wantResponse = true;
		timeoutStart = LocalDateTime.now();
	}
	
	public void stopTimeout() {
		wantResponse = false;
		timeoutStart = null;
	}
	
	public void shutdown() {
		exit = true;
		try {
			out.close();
			in.close();
			socket.close();
		} catch (IOException e) {
			setChanged();
			notifyObservers(SHUTDOWN_ERROR + socket.getInetAddress());
		}
	}
	
	private static boolean argToBool(String s) {
		if (s.equals("1")) {
			return true;
		} else {
			return false;
		}
	}
}

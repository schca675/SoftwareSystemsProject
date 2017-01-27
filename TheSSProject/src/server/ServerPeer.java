package server;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;
import java.util.LinkedList;
import java.util.List;
import java.util.Observable;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

import client.ClientCapabilities;

public class ServerPeer extends Observable implements Runnable {
	private Socket socket;
	private BufferedReader in;
	private BufferedWriter out;
	private ServerTUI view;
	public List<String> messageBuffer;
	private int bullshitReceived = 0;
	private static final int BULLSHITTHRESHOLD = 3;
	
	private Lock lock;
	private Condition bufferIsEmpty;
	
	public void changeLock(Lock lock, Condition condition) {
		this.lock = lock;
		bufferIsEmpty = condition;
	}
	
	public ServerPeer(Socket socket, ServerTUI view) throws IOException {
		this.socket = socket;
		this.view = view;
		in = new BufferedReader(new InputStreamReader(socket.getInputStream()));
		out = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream()));
		messageBuffer = new LinkedList<String>();
		lock = new ReentrantLock();
		bufferIsEmpty = lock.newCondition();
	}
	
	public void sendMessage(String message) throws IOException {
		out.write(message);
		out.newLine();
		out.flush();
		view.printMessage(message);
	}
	
	public void run() {
		boolean exit = false;
		while (!exit) {
			try {
				String message = in.readLine();
				if (message != null) {
					lock.lock();
					messageBuffer.add(message);
					bufferIsEmpty.signalAll();
					setChanged();
					notifyObservers();
				}
			} catch (IOException e) {
				//TODO: Exception forwarding
				exit = true;
			} finally {
				lock.unlock();
			}
		}
	}
	
	public void parseMessage(String message) {
		String[] messageParts = message.split(" ");
		if (messageParts.length > 0 && Protocol.isDefinedClientCommand(messageParts[0])) {
			String command = messageParts[0];
			switch (command) {
				case Protocol.Client.SENDCAPABILITIES:
					if (messageParts.length == 10 && 
					(messageParts[3].equals("0") || messageParts[3].equals("1")) && 
					(messageParts[8].equals("0") || messageParts[8].equals("1")) && 
					(messageParts[9].equals("0") || messageParts[9].equals("1"))) {
						try {
							int numPlayers = Integer.parseInt(messageParts[1]);
							String name = messageParts[2];
							boolean roomSupport = argToBool(messageParts[3]);
							int maxXDim = Integer.parseInt(messageParts[4]);
							int maxYDim = Integer.parseInt(messageParts[5]);
							int maxZDim = Integer.parseInt(messageParts[6]);
							int winLength = Integer.parseInt(messageParts[7]);
							boolean chatSupport = argToBool(messageParts[8]);
							boolean autoRefresh = argToBool(messageParts[9]);
							ClientCapabilites caps = new ClientCapabilities(int amountOfPlayers, String playerName, boolean roomSupport, int maxXDim, 
									int maxYDim, int maxZDim, int winLength, boolean chatSupport, boolean autoRefresh);
							// Send to observer
						} catch (NumberFormatException e) {
							bullshitReceived++;
							sendMessage(ServerMessages.genErrorIllegalStringString());
						}
					} else {
						bullshitReceived++;
						sendMessage(ServerMessages.genErrorIllegalStringString());
					}
					break;
				case Protocol.Client.MAKEMOVE:
					if (messageParts.length == 3) {
						try {
							int x = Integer.parseInt(messageParts[1]);
							int y = Integer.parseInt(messageParts[2]);
							Coordinates c = new Coordinates(x, y);
							// Send to observer
						} catch (NumberFormatException e) {
							sendMessage(ServerMessages.genErrorIllegalStringString());
						}
					} else {
						bullshitReceived++;
						sendMessage(ServerMessages.genErrorIllegalStringString());
					}
					break;
				default:
					bullshitReceived++;
					sendMessage(ServerMessages.genErrorInvalidCommandString());
					break;
			}
		} else {
			sendMessage(ServerMessages.genErrorInvalidCommandString());
		}
	}
	
	public void shutdown() {
		
	}
	
	private boolean argToBool(String s) {
		if (s.equals("1")) {
			return true;
		} else {
			return false;
		}
	}
}

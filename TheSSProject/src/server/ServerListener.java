package server;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.Observable;

public class ServerListener extends Observable implements Runnable {
	public static final String INIT_ERROR = "Connection listener can not be created";
	public static final String LISTEN_ERROR = "Error while waiting for connection";
	public static final String SHUTDOWN_ERROR = "Error while shutting down connection listener";
	private int port;
	private ServerSocket listener;
	boolean exit = false;
	ServerTUI view;
	
	public ServerListener(int port, ServerTUI view) {
		this.port = port;
		this.view = view;
	}
	
	public void run() {
		try {
			listener = new ServerSocket(port);
		} catch (IOException e) {
			exit = true;
			notifyObservers(INIT_ERROR);
		}
		while (!exit) {
			try {
				Socket socket = listener.accept();
				setChanged();
				notifyObservers(socket);
			} catch (IOException e) {
				notifyObservers(LISTEN_ERROR);
				exit = true;
			}
		}
	}
	
	public void shutdown() {
		try {
			exit = true;
			listener.close();
		} catch (IOException e) {
			notifyObservers(SHUTDOWN_ERROR);
		}
	}
}

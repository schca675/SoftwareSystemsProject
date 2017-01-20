package controller;

import java.io.IOException;
import java.net.ServerSocket;
import java.util.Observable;

public class ServerListener extends Observable implements Runnable {
	public static final String INIT_ERROR = "Connection listener can not be created";
	public static final String LISTEN_ERROR = "Error while waiting for connection";
	public static final String SHUTDOWN_ERROR = "Error while shutting down connection listener";
	private int port;
	private ServerSocket listener;
	boolean exit = false;
	
	public ServerListener(int port, view.ServerTUI view) {
		this.port = port;
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
				notifyObservers(listener.accept());
			} catch (IOException e) {
				notifyObservers(LISTEN_ERROR);
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

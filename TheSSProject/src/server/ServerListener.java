package server;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;

public class ServerListener  implements Runnable {
	public static final String INIT_ERROR = "Connection listener cannot be created, "
			+ "shutting down...";
	public static final String LISTEN_ERROR = "Error while waiting for connection, "
			+ "shutting down...";
	public static final String SHUTDOWN_ERROR = "Error while shutting down connection listener";
	
	private int port;
	private ServerSocket listener;
	private Server server;
	private ServerTUI view;
	boolean exit = false;
	
	public ServerListener(int port, ServerTUI view, Server server) {
		this.port = port;
		this.server = server;
		this.view = view;
	}
	
	public void run() {
		try {
			listener = new ServerSocket(port);
		} catch (IOException e) {
			view.printMessage(INIT_ERROR);
			shutdown();
		}
		while (!exit) {
			try {
				Socket socket = listener.accept();
				view.printMessage("Client connected from " + 
						socket.getInetAddress().getHostAddress() + ":" + socket.getPort());
				server.initConnection(socket);
			} catch (IOException e) {
				view.printMessage(LISTEN_ERROR);
				shutdown();
			}
		}
	}
	
	public void shutdown() {
		try {
			exit = true;
			listener.close();
			view.printMessage("Connection listener shut down, no new connections will be "
					+ "made");
		} catch (IOException e) {
			view.printMessage(SHUTDOWN_ERROR);
		}
	}
}
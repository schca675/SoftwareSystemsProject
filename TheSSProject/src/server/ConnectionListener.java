package server;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;

import view.ServerTUI;

public class ConnectionListener  implements Runnable {
	public static final String INIT_ERROR = "Connection listener cannot be created, "
			+ "shutting down...";
	public static final String LISTEN_ERROR = "Error while waiting for connection, "
			+ "shutting down...";
	public static final String SHUTDOWN_ERROR = "Error while shutting down connection listener";
	
	private ServerSocket listener;
	private Server server;
	private ServerTUI view;
	boolean exit = false;
	
	public ConnectionListener(int port, ServerTUI view, Server server) throws IOException {
		this.server = server;
		this.view = view;
		listener = new ServerSocket(port);
	}
	
	public void run() {
		while (!exit) {
			try {
				Socket socket = listener.accept();
				view.printMessage(socket.getInetAddress().getHostAddress() + ":" + 
						socket.getPort() + " connected");
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
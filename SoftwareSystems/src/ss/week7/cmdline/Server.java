
package ss.week7.cmdline;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;

/**
 * Server. 
 * @author  Theo Ruys
 * @version 2005.02.21
 */
public class Server {
    private static final String USAGE
        = "usage: " + Server.class.getName() + " <name> <port>";

    /** Starts a Server-application. */
    public static void main(String[] args) {
    	if (args.length != 2) {
    		System.out.println(USAGE);
    		System.exit(0);
    	}
    	
    	String name = args[0];
    	int port = 0;
    	ServerSocket serverSock = null;
    	Socket sock = null;
    	
    	//Parse port argument
    	try {
    		port = Integer.parseInt(args[1]);
    		System.out.println("Arguments OK");
    	} catch (NumberFormatException e) {
    		System.out.println(USAGE);
    		System.out.println("ERRROR: port " + args[1] + " is not an integer");
    		System.exit(0);
    	}
    	
    	//Try to open a server socket
    	try {
    		serverSock = new ServerSocket(port);
    		System.out.println("Socket created");
    	} catch (IOException e) {
    		System.out.println("ERROR: could not create a socket at port " + port);
    	}
    	
    	//Listen for a connection
    	try {
    		sock = serverSock.accept();
    		System.out.println("Connection accepted");
    	} catch (IOException e) {
    		System.out.println("ERROR: error while waiting for a connection");
    	}
    	
    	//Creates a peer for communication
    	try {
    		Peer server = new Peer(name, sock);
    		Thread streamInputHandler = new Thread(server);
    		streamInputHandler.start();
    		server.handleTerminalInput();
    		server.shutDown();
    	} catch (IOException e) {
    		System.out.println("ERROR: communication error");
    	}
    	
    }

} // end of class Server

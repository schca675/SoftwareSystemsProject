package ss.week7.cmdline;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;
import java.net.SocketException;

/**
 * Peer for a simple client-server application.
 * @author  Theo Ruys
 * @version 2005.02.21
 */
public class Peer implements Runnable {
    public static final String EXIT = "exit";

    protected String name;
    protected Socket sock;
    protected BufferedReader in;
    protected BufferedWriter out;


    /*@
       requires (nameArg != null) && (sockArg != null);
     */
    /**
     * Constructor. creates a peer object based in the given parameters.
     * @param   nameArg name of the Peer-proces
     * @param   sockArg Socket of the Peer-proces
     */
    public Peer(String nameArg, Socket sockArg) throws IOException {
    	this.name = nameArg;
    	this.sock = sockArg;
    	in = new BufferedReader(new InputStreamReader(sockArg.getInputStream()));
    	out = new BufferedWriter(new OutputStreamWriter(sockArg.getOutputStream()));
    }

    /**
     * Reads strings of the stream of the socket-connection and
     * writes the characters to the default output.
     */
    public void run() {
    	String message;
    	try {
    		message = in.readLine();
    		while (message != "" && message != null && !message.equals("exit")) {
    			System.out.println(message);
    			message = in.readLine();
    		}
    		this.shutDown();
    	} catch (IOException e) {
    		this.shutDown();
    		
    	}
    }


    /**
     * Reads a string from the console and sends this string over
     * the socket-connection to the Peer process.
     * On Peer.EXIT the method ends
     */
    public void handleTerminalInput() {
    	boolean stop = false;
    	while (!stop) {
			String input =  readString("Enter input:");
			
			try {
				out.write(input);
				out.newLine();
				out.flush();
				
				if (input.equals("exit")) {
					this.shutDown();
					break;
				}
			} catch (IOException e) {
				System.out.println("Connection terminated.");
				stop = true;
			}
    			
    	}
    	/*String input = readString("Enter input");
    	while (!input.equals("exit")) {
			try {
				out.write(input);
				out.newLine();
				out.flush();
				input = readString("Enter input");
			} catch (IOException e) {
				System.out.println("Socket is closed handleTerminal in while" + e.getMessage());
				input = "exit";
			}
    	}
    	try {
			out.write(input);
			out.newLine();
			out.flush();
		} catch (IOException e) {
			System.out.println("IO Exception: handle Terminal : " + e.getMessage());
		} finally {
			this.shutDown();
		} */
/*    	Scanner scanny = new Scanner(System.in);
    	String line = "strt";
    	while (!line.equals("exit")) {
    		if (scanny.hasNextLine()) {
    			line = scanny.nextLine();
    			try {
    				out.write(line);
    				out.newLine();
    				out.flush();
    			} catch (IOException e) {
    				System.err.println(e.getMessage());
    			}
    		}
    	}
    	scanny.close();*/
    }

    /**
     * Closes the connection, the sockets will be terminated.
     */
    public void shutDown() {
    	try {
    		out.close();
        	in.close();
        	sock.close();
    	} catch (IOException e) {
    		System.out.println("Problems while the shut down");
    	}
    }

    /**  
     * Returns name of the peer object.
     */
    public String getName() {
        return name;
    }

    /**  
     * Read a line from the default input.
     */
    static public String readString(String tekst) {
        System.out.print(tekst);
        String antw = null;
        try {
            BufferedReader in = new BufferedReader(new InputStreamReader(
                    System.in));
            antw = in.readLine();
        } catch (IOException e) {
        }

        return (antw == null) ? "" : antw;
    }
}

package testing;

import java.io.IOException;
import java.net.InetAddress;

public class ServerTestFirst {
	
	/**
	 * Executing the server Test, by following the protocol until sending illegal moves.
	 * @param args arguments for the main, unused.
	 */
	public static void main(String[] args) {
		// A Server must be started on this laptop with port number 2000.
		
		System.out.println("First Test \n");
		ServerTesterClient testerA = new ServerTesterClient("A");
		ServerTesterClient testerB = new ServerTesterClient("B");
		try {
			//First player.
			testerA.connect(InetAddress.getByName("localhost"), 2000);
			System.out.println("Tester A is connected");
			//Server should send its capabilities.
			testerA.read();
			//Client has to send its capabilities.
			testerA.write("sendCapabilities 2 Mike 0 4 4 4 4 0 0");
			//Server should send an ID back.
			testerA.read();
			
			//Second player.
			testerB.connect(InetAddress.getByName("localhost"), 2000);
			System.out.println("Tester B is connected");
			//Server should send its capabilities.
			testerB.read();
			//Client has to send its capabilities.
			testerB.write("sendCapabilities 2 Ben 0 4 4 4 4 0 0");
			//Server should send an ID back.
			testerB.read();
			
			//Server should start a game.
			testerA.read();
			testerB.read();
			testerA.write("makeMove 2 2");
			testerA.read();
			testerB.read();
			testerB.write("makeMove 2 2");
			testerA.read();
			testerB.read();
			testerA.write("makeMove 2 2");
			testerA.read();
			testerB.read();
			testerB.write("makeMove 2 2");
			testerA.read();
			testerB.read();
			testerA.write("makeMove 2 2");
			testerA.read();
			testerB.read();
			testerB.write("makeMove 2 2");
			// At some point the testers write an illegal move 
			// and the server has to handle that
			testerA.shutDown();
			testerB.shutDown();
		} catch (NullPointerException | IOException e) {
			System.out.println("Exceptions in this class during testing");
		}		  
	}
}

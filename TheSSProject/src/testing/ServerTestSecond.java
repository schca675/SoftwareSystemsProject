package testing;

import java.io.IOException;
import java.net.InetAddress;

public class ServerTestSecond {

	/**
	 * Test the server by writing invalid messages to it.
	 * @param args arguments for the main, unused.
	 */
	public static void main(String[] args) {
		System.out.println("\n\nSecond Test \n");
		// Tester E is only giving invalid input.
		ServerTesterClient testerE = new ServerTesterClient("E");
		try {
			//First player who will not send a good capability message.
			testerE.connect(InetAddress.getByName("localhost"), 2000);
			System.out.println("Tester E is connected");
			//Server should send its capabilities.
			testerE.read();
			//Client sends wrong capabilities and wrong messages and 
			// should be disconnected after the third stupid message.
			testerE.write("sendCapabilities 2 Mike 0 4 4 4 4 0 0 0");
			testerE.read();
			testerE.write("I am writing stupid stuff");
			testerE.read();
			testerE.write("I am still writing stupid stuff and should now be disconnected.");
			testerE.read();
			testerE.write("Can I still write stuff?");
			testerE.read();
			testerE.shutDown();
		} catch (NullPointerException | IOException e) {
			System.out.println("Exceptions in this class during testing");
		}
	}
}

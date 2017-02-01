package testing;

import java.io.IOException;
import java.net.InetAddress;

public class ServerGameTest {
	
	/**
	 * Executing the server Test, following the schema of.
	 * @param args not given.
	 */
	public static void main(String[] args) throws InterruptedException {
		// A Server must be started on this laptop with port number 2000.
		ServerTesterClient testerA = new ServerTesterClient();
		ServerTesterClient testerB = new ServerTesterClient();
		try {
			//First player.
			testerA.connect(InetAddress.getByName("localhost"), 2000);
			//Server should send its capabilities.
			testerA.read();
			//Client has to send its capabilities.
			testerA.write("sendCapabilities 2 Mike 0 4 4 4 4 0 0");
			//Server should send an ID back.
			testerA.read();
			
			//Second player.
			testerB.connect(InetAddress.getByName("localhost"), 2000);
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
		
		// The testers now write 
		ServerTesterClient testerC = new ServerTesterClient();
		ServerTesterClient testerD = new ServerTesterClient();
		ServerTesterClient testerE = new ServerTesterClient();
		try {
			//First player who will not send a good capability message.
			testerE.connect(InetAddress.getByName("localhost"), 2000);
			//Server should send its capabilities.
			testerE.read();
			//Client sends wrong capabilities and should be disconnected
			testerE.write("sendCapabilities 2 Mike 0 4 4 4 4 0 0 0");
			//Server should send an ID back.
			testerE.read();
			testerE.write("I am writing stupid stuff");
			
			//Second player.
			testerD.connect(InetAddress.getByName("localhost"), 2000);
			//Server should send its capabilities.
			testerD.read();
			//Client has to send its capabilities.
			testerD.write("sendCapabilities 2 Ben 0 4 4 4 4 0 0");
			//Server should send an ID back.
			testerD.read();
			
			//Third player.
			testerC.connect(InetAddress.getByName("localhost"), 2000);
			//Server should send its capabilities.
			testerC.read();
			//Client has to send its capabilities.
			testerC.write("sendCapabilities 2 Ben 0 4 4 4 4 0 0");
			//Server should send an ID back.
			testerC.read();
			
			//Server should start a game.
			Thread.sleep(100);
			testerC.read();
			testerD.read();
			testerC.write("makeMove 2 8");
			Thread.sleep(100);
			testerC.read();
			testerD.read();
			testerD.write("makeMove 2 2");
			Thread.sleep(100);
			testerC.read();
			testerD.read();
			testerC.write("makeMove 2 3");
			Thread.sleep(100);
			testerC.read();
			testerD.read();
			testerD.write("makeMove 2 2");
			Thread.sleep(100);
			testerC.read();
			testerD.read();
			testerC.write("makeMove 2 3");
			Thread.sleep(100);
			testerD.read();
			testerC.read();
			testerD.write("makeMove 2 2");
			Thread.sleep(100);
			testerC.read();
			testerD.read();
			testerC.write("makeMove 2 3");
			Thread.sleep(100);
			testerD.read();
			testerC.read();
			testerD.write("makeMove 2 2");
			Thread.sleep(100);
			testerC.read();
			testerD.read();
			testerC.write("makeMove 2 3");
			Thread.sleep(100);
			testerD.read();
			testerC.read();
			testerD.write("makeMove 2 2");
			Thread.sleep(100);
			testerC.read();
			testerD.read();
			testerC.write("makeMove 2 3");
			Thread.sleep(100);
			testerD.read();
			testerC.read();
			testerD.write("makeMove 2 2");
			Thread.sleep(100);
			testerC.read();
			testerD.read();
			testerC.write("makeMove 2 3");
			Thread.sleep(100);
			testerD.read();
			testerC.read();
			testerD.write("makeMove 2 2");
			Thread.sleep(100);
			// At some point tester C wants to write an illegal move and 
			// then wants to write more moves. It should get disconnected
			System.out.println("The clients are now shutting down");
			testerE.shutDown();
			testerC.shutDown();
			testerD.shutDown();
		} catch (NullPointerException | IOException e) {
			System.out.println("Exceptions in this class during testing");
		}
		  
	}
}

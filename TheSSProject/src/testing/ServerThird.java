package testing;

import java.io.IOException;
import java.net.InetAddress;

public class ServerThird {

	/**
	 * Tests the server: a player first sends a wrong message and gets another chance to 
	 * write the capabilities. Second try is right, a second player connects and a game is started.
	 * @param args
	 * @throws InterruptedException
	 */
	public static void main(String[] args) throws InterruptedException {
		System.out.println("\n\nThird Test \n");
		ServerTesterClient testerC = new ServerTesterClient("C");
		ServerTesterClient testerD = new ServerTesterClient("D");
		try {
			//Second player.
			testerD.connect(InetAddress.getByName("localhost"), 2000);
			System.out.println("Tester D is connected");
			//Server should send its capabilities.
			testerD.read();
			//Client has to send its capabilities but sends wrong stuff.
			testerD.write("Not right for the first time");
			// Client has 3 chances to send sth right so it should now still work.
			testerD.write("sendCapabilities 2 Ben 0 4 4 4 4 0 0");
			//Server should send an ID back.
			testerD.read();
			
			//Third player.
			testerC.connect(InetAddress.getByName("localhost"), 2000);
			System.out.println("Tester C is connected");
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
			testerD.write("makeMove -1 2");
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
			testerC.shutDown();
			testerD.shutDown();
		} catch (NullPointerException | IOException e) {
			System.out.println("Exceptions in this class during testing");
		}
	}
}

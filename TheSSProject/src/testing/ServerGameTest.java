package testing;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import model.ComputerPlayer;
import model.Player;
import server.ClientCapabilitiesStruct;
import server.Server;
import view.ServerTUI;

public class ServerGameTest {
	
	/**
	 * Executing the server Test, following the schema of.
	 * @param args not given.
	 */
	public static void main(String[] args) {
		ServerTUI view = new ServerTUI();
		int port = 2000;
		boolean extensions = false;
		Player a = new ComputerPlayer(1);
		Player b = new ComputerPlayer(2);
		List<Player> players = new ArrayList<Player>();
		players.add(a);
		players.add(b);
		ClientCapabilitiesStruct ca = new ClientCapabilitiesStruct(2, "a", false, 
				4, 4, 4, 4, false, false);
		ClientCapabilitiesStruct cb = new ClientCapabilitiesStruct(2, "b", false, 
				4, 4, 4, 4, false, false);
		Map<Player, ClientCapabilitiesStruct> capabilities = new HashMap();
		capabilities.put(a, ca);
		capabilities.put(b, cb);
		try {
			Server server = new Server(port, extensions, view);
			server.listenForConnections();
		} catch (IOException e) {
			System.out.println("Problems while setting up the server: " + e.getMessage());
		}
		  
	}
}

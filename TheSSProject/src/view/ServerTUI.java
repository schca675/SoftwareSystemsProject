package view;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

public class ServerTUI {
	BufferedReader inputReader;

	/**
	 * Create a new ServerTUI.
	 */
	public ServerTUI() {
		inputReader = new BufferedReader(new InputStreamReader(System.in));
	}
	
	/**
	 * Print a message to the terminal.
	 * @param message message to print to the terminal.
	 */
	public synchronized void printMessage(String message) {
		synchronized (System.out) {
			System.out.println(message);
		}
	}
	
	/**
	 * Request the portnumber on which the server should open a connection.
	 * @return the portnumber for the server connection.
	 */
	//@ ensures \result >= 0 && \result <= 65535;
	public int requestPortNumber() {
		printMessage("Please enter a port number to bind to, from 1025 up to 65535.");
		while (true) {
			try {
				String input = inputReader.readLine();
				if (Integer.parseInt(input) >= 1025 && Integer.parseInt(input) 
						<= 65535) {
					return Integer.parseInt(input);
				}
			} catch (NumberFormatException e) {	
			} catch (IOException e) {
				printMessage("IOException while reading port number, terminating...");
				//This is the very beginning of startup, if it is impossible to read this exiting 
				//might be best
				System.exit(0);
			}
		}
	}
	
	/**
	 * Request if the server should enable the extensions or not.
	 * @return true if the extensions should be enabled, false if not.
	 */
	public boolean requestExtensions() {
		printMessage("Enable extensions: 'yes' for extensions, 'no' otherwise (case-sensitive).");
		printMessage("Extensions currently implemented: larger board, infinite height, "
				+ "more players");
		while (true) {
			try {
				String input = inputReader.readLine();
				if (input.equals("yes")) {
					return true;
				} else if (input.equals("no")) {
					return false;
				}
			} catch (IOException e) {
				printMessage("IOException while reading extensions input, terminating...");
				//This is the very beginning of startup, if it is impossible to read this exiting 
				//might be best
				System.exit(0);
			}
		}
	}
}

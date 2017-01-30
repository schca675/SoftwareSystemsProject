package server;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.Observable;
import java.util.Observer;

public class ServerTUI implements Observer {
	BufferedReader inputReader;

	public ServerTUI() {
		inputReader = new BufferedReader(new InputStreamReader(System.in));
	}
	
	/**
	 * Prints a given message on the Terminal screen.
	 * @param message Message to print on the screen.
	 */
	@Override
	public synchronized void update(Observable o, Object arg) {
		printMessage(((ClientHandler) o).toString() + (String) arg);
	}
	
	public synchronized void printMessage(String message) {
		System.out.println(message);
	}
	
	//@ ensures \result >= 0 && \result <= 65535;
	public int requestPortNumber() {
		printMessage("Please enter a port number to bind to, from 0 up to 65535.");
		while (true) {
			try {
				String input = inputReader.readLine();
				if (Integer.parseInt(input) >= 0 && Integer.parseInt(input) 
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

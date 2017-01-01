package View;

import java.util.Scanner;

import controller.Game;
import model.HumanPlayer;
import model.Player;
import model.PlayerID;

public class FourWins {
	public static void main(String[] args) {
		if (args.length == Game.NUMBER_PLAYERS) {
			// Strategy strategy;
			PlayerID playerID = PlayerID.O;
			Player a = new HumanPlayer(args[0], playerID);
			Player b = new HumanPlayer(args[1], playerID.other());
			
			// code needed to enlarge the dimensions)
			/*if (!readBoolean("Do you want to play with default board?", "y", "n")) {
			System.out.println("Please enter your dimensions.");
			// code to follow
			} else {
			} */
			
			Game game = new Game(a, b);
			game.start();
		}
	}
	
	/**
	 * Determines whether the user enters Yes or No.
	 * @param message Message to print on the screen.
	 * @param yes String that should be interpreted as "yes".
	 * @param no String that should be interpreted as "no".
	 * @return true or false, depending on the input of the user.
	 */
	public static Boolean readBoolean(String message, String yes, String no) {
		Boolean compared = false;
		Boolean result = null;
		String scanned = "";
		Scanner scanny = new Scanner(System.in);
		System.out.println(message);
		while (!compared) {
			System.out.println("Please answer in the format (" + yes + "/" + no + ") : " 
					+ yes + " for yes or " + no + " for no");
			if (scanny.hasNext()) {
				scanned = scanny.next();
				if (scanned.equals(yes)) {
					result = true;
				} else if (scanned.equals(no)) {
					result = false;
				}
			}
			if (result != null) {
				compared = true;
			}
		}
		return result;
	}

}

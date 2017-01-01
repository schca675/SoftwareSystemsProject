package controller;

import java.util.Random;
import java.util.Scanner;

import model.Board;
import model.Coordinates;
import model.Player;
import model.PlayerID;

public class Game {
	
	// <------ Constants ------>
	
	public static final int NUMBER_PLAYERS = 2;
	
	// <------ Instance variables ------>
	
	//@ private invariant board != null;
	//@ private invariant players !=null && players.length == NUMBER_PLAYERS;
	//@ private invariant (\forall int i; i >= 0 && i < NUMBER_PLAYERS; players[i] != null);
	//@ private invariant currentPlayerIndex >= 0 && currentPlayerIndex < NUMBER_PLAYERS;
	private Board<PlayerID> board;
	private Player[] players;
	private int currentPlayerIndex;
	
	// <------ Constructors ------>
	
	/**
	 * Create a game with default setting and rules and a random starter.
	 * 
	 * @param player1 Player 1
	 * @param player2 Player 2
	 */
	//@ requires player1 != null && player2 != null;
	public Game(Player player1, Player player2) {
		board = new Board<PlayerID>();
		players[0] = player1;
		players[1] = player2;
		currentPlayerIndex = randomStarter();	
	}
	
	/**
	 * Creates a game with specified dimensions of the board, winning length and random starter.
	 * @param player1 Player 1
	 * @param player2 Player 2
	 * @param xDim X dimension of the board
	 * @param yDim Y dimension of the board
	 * @param zDim Z dimension of the board, -1 specifies unlimited
	 * @param winningLength Connected pieces required to win the game
	 */
	//@ requires player1 != null && player2 != null;
	/*@ requires winningLength <= xDim || winningLength <= yDim 
	  @ || (zDim > 0 && winningLength <= zDim) || (zDim == Board.UNLIMITED_Z);
	*/
	//@ requires xDim > 0 && yDim > 0 && (zDim > 0 || zDim == -1) && winningLength > 0;
	public Game(Player player1, Player player2, int xDim, int yDim, int zDim, int winningLength) {
		board = new Board<PlayerID>(xDim, yDim, zDim, winningLength);
		players[0] = player1;
		players[1] = player2;
		currentPlayerIndex = randomStarter();
	}
	
	// <------ Queries ------>
	
	/**
	 * Determines a random starter of the game.
	 * @return the index of the starting player
	 */
	//@ ensures \result >= 0 && \result < NUMBER_PLAYERS;
	public int randomStarter() {
		Random random = new Random();
		return random.nextInt(NUMBER_PLAYERS);	
	}
	
	// <------ Commands ------>
	
	/** 
	 * Resets the game.
	 * Same players get an empty board with a random starter.
	 */
	private void reset() {
		currentPlayerIndex = randomStarter();
		board.reset();
	}
	
	/**
	 * Starts the 4 wins game.
	 * After each ended game, the player(s) can decide whether to continue or not.
	 * The method runs until a negative response is given.
	 */
	public void start() {
		boolean playing = true;
		while (playing) {
			reset();
			play();
		    playing = readBoolean("Do you want to play another time?", "y", "n");	
		}
	}
	/**
	 * Runs the game.
	 * Game starts with an empty board and 
	 * finishes when there is a winner or a draw (board is full).
	 */
	// not checked yet.
	public void play() {
		currentSituation();
		boolean winning = false;
		Player currentplayer = players[currentPlayerIndex];
		while (!winning && !board.isFull()) {
			Coordinates coord = currentplayer.determineMove(board);
			currentplayer.makeMove(board, coord);
			winning = board.hasWon(coord.getX(), coord.getY(), 
					board.getTowerHeight(coord.getX(), coord.getY()));
			if (!winning) {
				currentPlayerIndex = currentPlayerIndex + 1 % NUMBER_PLAYERS;
				currentplayer = players[currentPlayerIndex];
			}
			currentSituation();
		}
		if (winning) {
			//  The currentplayer is the winner.
			System.out.println("Player " + currentplayer.getName() + " with ID " 
					+ currentplayer.getPlayerID() + " is the winner!");
		} else {
			// The board is full, so there is a draw.
			System.out.println("Draw. There is no winner");
		}
	}
	
	/**
	 * Determines whether the user enters Yes or No.
	 * @param message Message to print on the screen.
	 * @param yes String that should be interpreted as "yes".
	 * @param no String that should be interpreted as "no".
	 * @return true or false, depending on the input of the user.
	 */
	public Boolean readBoolean(String message, String yes, String no) {
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
	
	//To do: board.ToString does not really exist yet
	/**
	 * Prints the current Situation of the game.
	 */
	public void currentSituation() {
		System.out.println("Current game situation: ");
		System.out.println(board.toString());
	}
}

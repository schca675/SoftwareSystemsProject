package controller;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import java.util.Scanner;

import model.Board;
import model.ComputerPlayer;
import model.IllegalCoordinatesException;
import model.Player;
import model.TowerCoordinates;

public class Game {
	
	// <------ Instance variables ------>
	
	//@ private invariant board != null;
	//@ private invariant players != null && (players.size() == numberOfPlayers);
	//@ private invariant (\forall int i; i >= 0 && i < numberOfPlayers; players.get(i)!= null);
	//@ private invariant currentPlayerIndex >= 0 && currentPlayerIndex < numberOfPlayers;
	private Board board;
	private List<Player> players;
	private int currentPlayerIndex;
	public final int numberOfPlayers;
	
	// <------ Constructors ------>
	
	/**
	 * Create a game with default setting and rules and a random starter.
	 * 
	 * @param player1 Player 1 
	 * @param player2 Player 2
	 */
	/*@ requires players != null && 
	  @ (\forall int i; i >= 0 && i < numberOfPlayers; players.get(i)!= null);
	*/
	public Game(List<Player> players) {
		board = new Board();
		this.players = new ArrayList<Player>(players.size()); 
		this.players.addAll(players);
		currentPlayerIndex = randomStarter();
		numberOfPlayers = players.size();
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
	/*@ requires players != null && 
	  @ (\forall int i; i >= 0 && i < numberOfPlayers; players.get(i)!= null);
	  @ requires winningLength <= xDim || winningLength <= yDim 
	  @ || (zDim > 0 && winningLength <= zDim) || (zDim == Board.UNLIMITED_Z);
	  @ requires xDim > 0 && yDim > 0 && (zDim > 0 || zDim == -1) && winningLength > 0;
	*/
	public Game(List<Player> players, int xDim, int yDim, int zDim, int winningLength) {
		board = new Board(xDim, yDim, zDim, winningLength);
		this.players = new ArrayList<Player>(players.size()); 
		this.players.addAll(players);
		currentPlayerIndex = randomStarter();
		numberOfPlayers = players.size();
	}
	
	// <------ Queries ------>
	
	/**
	 * Determines a random starter of the game.
	 * @return the index of the starting player
	 */
	//@ ensures \result >= 0 && \result < numberOfPlayers;
	public int randomStarter() {
		Random random = new Random();
		return random.nextInt(numberOfPlayers);	
	}
	
	// <------ Commands ------>
	
	/**
	 * Starts the game.
	 */
	public void start() {
		play();
	}
	
	/**
	 * Runs the game.
	 * Game starts with an empty board and 
	 * finishes when there is a winner or a draw (board is full).
	 * If one of the clients is making an invalid move, 
	 * he is replaced by a Computer player with random strategy.
	 * If a computer player tries an invalid move //TODO
	 */
	// not checked yet.
	public void play() {
		currentSituation();
		boolean winning = false;
		Player currentplayer = players.get(currentPlayerIndex);
		while (!winning && !board.isFull()) {
			TowerCoordinates coord = currentplayer.determineMove(board);
			try {
				board.makeMove(coord.getX(), coord.getY(), currentplayer.playerID);
			} catch (IllegalCoordinatesException e) {
				currentplayer = new ComputerPlayer(currentplayer.playerID);
				coord = ((ComputerPlayer) currentplayer).determineMove(board);
				try {
					board.makeMove(coord.getX(), coord.getY(), currentplayer.playerID);
				} catch (IllegalCoordinatesException ex) {
					//TODO
				}
				
			}
			winning = board.hasWon(coord.getX(), coord.getY());
			if (!winning) {
				// following code only works because we have 2 players
				currentPlayerIndex = 1 - currentPlayerIndex;
				currentplayer = players.get(currentPlayerIndex);
			}
			currentSituation();
		}
		if (winning) {
			//  The currentplayer is the winner.
			System.out.println("Player " + currentplayer.name + " with Player ID " 
					+ currentplayer.playerID + " is the winner!");
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

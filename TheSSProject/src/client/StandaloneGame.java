package client;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import java.util.Scanner;

import model.Board;
import model.ComputerPlayer;
import model.HumanPlayer;
import model.IllegalBoardConstructorArgumentsException;
import model.IllegalCoordinatesException;
import model.Player;
import model.TowerCoordinates;

public class StandaloneGame {
	
	// <------ Instance variables ------>
	
	//@ private invariant board != null;
	//@ private invariant players != null && (players.size() == numberOfPlayers);
	// The line below is the one the JML compiler complains about, specifically the last part. 
	// For JML, isn't this assumed by default?
	// private invariant (\forall int i; i >= 0 && i < numberOfPlayers; players.get(i) != null);
	//@ private invariant currentPlayerIndex >= 0 && currentPlayerIndex < numberOfPlayers;
	private Board board;
	private List<Player> players;
	private int currentPlayerIndex;
	public final int numberOfPlayers;
	
	// <------ Constructors ------>
	
	/**
	 * Create a game with default setting and rules and a random starter.
	 * 
	 * @param players Players to play this game
	 */
	/*@ requires players != null && 
	  @ (\forall int i; i >= 0 && i < numberOfPlayers; players.get(i)!= null);
	*/
	public StandaloneGame(List<Player> players) {
		board = new Board();
		this.players = new ArrayList<Player>(players.size()); 
		this.players.addAll(players);
		currentPlayerIndex = randomStarter();
		numberOfPlayers = players.size();
	}
	
	/**
	 * Creates a game with specified dimensions of the board, winning length and random starter.
	 * @param players Players to play this game
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
	public StandaloneGame(List<Player> players, int xDim, int yDim, int zDim, int winningLength) {
		try {
			board = new Board(xDim, yDim, zDim, winningLength);
		} catch (IllegalBoardConstructorArgumentsException e) {
			System.err.println(e.getMessage());
		}
		this.players = players;
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
		return 0;
/*		Random random = new Random();
		return random.nextInt(numberOfPlayers);	*/
	}
	
	// <------ Commands ------>
	
	public static void main(String[] args) {
		List<Player> players = new ArrayList<Player>(2);
		players.add(new HumanPlayer("Henk", 0));
		players.add(new ComputerPlayer(1));
		StandaloneGame game = new StandaloneGame(players);
		game.play();
	}
	
	/**
	 * Runs the game.
	 * Game starts with an empty board and 
	 * finishes when there is a winner or a draw (board is full).
	 * If one of the clients is making an invalid move, 
	 * he is replaced by a Computer player with random strategy.
	 * If a computer player tries an invalid move //TODO
	 */
	public void play() {
		currentSituation();
		boolean gameOver = false;
		int attempts = 0;
		while (!gameOver) {
			Player currentPlayer = players.get(currentPlayerIndex);
			TowerCoordinates coords;
			if (currentPlayer instanceof HumanPlayer) {
				coords = requestHumanMove(currentPlayer.playerID);
			} else {
				ComputerPlayer computerPlayer = (ComputerPlayer) currentPlayer;
				coords = computerPlayer.determineMove(board);
			}
			try {
				board.makeMove(coords.getX(), coords.getY(), currentPlayer.playerID);
				if (board.hasWon(coords.getX(), coords.getY())) {
					System.out.println("Player " + currentPlayer.name + " has won");
					gameOver = true;
				} else if (board.isFull()) {
					System.out.println("Draw, board is full");
					gameOver = true;
				} else {			
					currentPlayerIndex = currentPlayerIndex + 1;
					currentPlayerIndex = currentPlayerIndex % numberOfPlayers;
					attempts = 0;
				}
			} catch (NullPointerException e) {
				attempts++;
			} catch (IllegalCoordinatesException e) {
				attempts++;
				if (currentPlayer instanceof HumanPlayer) {
					System.out.println(e.getMessage());
				}
			} finally {
				if (attempts > 3) {
					gameOver = true;
				}
				currentSituation();
			}
		}
	}
	
	public TowerCoordinates requestHumanMove(int playerID) {
		String message = "Player " + playerID + ", make your move. Enter in format: x y";
		System.out.println(message);
		BufferedReader reader = new BufferedReader(new InputStreamReader(System.in));
		try {
			String[] splitInput = reader.readLine().split(" ");
			if (splitInput.length == 2 && splitInput[0].length() == 1 
					&& splitInput[1].length() == 1) {
				int x = Integer.parseInt(splitInput[0]);
				int y = Integer.parseInt(splitInput[1]);
				return new TowerCoordinates(x, y);
			}
		} catch (NumberFormatException e) {
			System.out.println(message);
		} catch (IOException e) {
			System.err.println(e.getMessage());
		}
		return null;
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

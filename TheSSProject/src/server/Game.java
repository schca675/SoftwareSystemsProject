package server;

import java.util.List;
import java.util.Map;
import java.util.Observable;
import java.util.Random;

import exc.IllegalBoardConstructorArgumentsException;
import exc.IllegalCoordinatesException;
import model.Board;
import model.ComputerPlayer;
import model.Player;
import model.SmartStrategy;
import model.TowerCoordinates;
import view.ServerTUI;

public class Game extends Observable implements Runnable {
	
	// <------ Instance variables ------>
	
	// The line below is the one the JML compiler complains about, specifically the last part. 
	// For JML, isn't this assumed by default?
	// private invariant (\forall int i; i >= 0 && i < numberOfPlayers; players.get(i) != null);
	// private invariant currentPlayerIndex >= 0 && currentPlayerIndex < numberOfPlayers;
	private List<Player> players;
	private Map<Player, ClientHandler> handlerMap;
	private /*@ spec_public @*/ Board board;
	private Player currentPlayer;
	private int currentPlayerIndex;
	private ServerTUI view;
	boolean exit = false;
	
	// <------ Constructors ------>
	
	/**
	 * Creates a game with specified dimensions of the board, winning length and random starter.
	 * @param players List of players
	 * @param handlerMap Map of players and their handlers
	 * @param rules Rules of the game
	 * @param view ServerTUI to communicate with the terminal.
	 */
	/*@ requires players.size() >= 2;
	  @ requires handlerMap.size() == players.size();
	  @ requires (\forall Player player; players.contains(player); handlerMap.containsKey(player));
	  @ requires rules.xDim >= 0 && rules.yDim >= 0 && rules.zDim >= 0 && rules.winLength > 0 && 
	  @ (rules.winLength <= rules.xDim || rules.winLength <= rules.yDim || rules.winLength <= 
	  @ rules.zDim || rules.zDim == 0);
	*/
	public Game(List<Player> players, Map<Player, ClientHandler> handlerMap, GameRulesStruct 
			rules, ServerTUI view) {
		try {
			this.view = view;
			this.players = players;
			this.handlerMap = handlerMap;
			board = new Board(rules.xDim, rules.yDim, rules.zDim, rules.winLength);
		} catch (IllegalBoardConstructorArgumentsException e) {
			//Something went awfully wrong
			view.printMessage(e.getMessage());
			shutdown();
		}
	}
	
	// <------ Commands ------>
	
	/**
	 * Starts the game.
	 */
	public void run() {
		play();
	}

	/**
	 * Sets current player to a random player.
	 */
	private void randomPlayer() {
		Random random = new Random();
		currentPlayerIndex = random.nextInt(players.size());
		currentPlayer = players.get(currentPlayerIndex);
	}
	
	/**
	 * Sets currentPlayer to the next player.
	 */
	private void nextPlayer() {
		currentPlayerIndex = (currentPlayerIndex + 1) % players.size();
		currentPlayer = players.get(currentPlayerIndex);
	}
	
	/**
	 * Notifies the players of game start, select a random player and requests the first move.
	 */
	private void play() {
		broadcastMessage(ServerMessages.genStartGameString(board.xDim, board.yDim, board.zDim, 
				board.winningLength, players));
		randomPlayer();
		requestMove(currentPlayer);
	}
	
	/**
	 * Requests a move from given player. Notifies all players of a new turn. 
	 * If a player has been replaced by a ComputerPlayer, its 
	 * determineMove method is called and processMove with the result.
	 * @param player Player whose turn it is
	 */
	//@ requires player != null; 
	private void requestMove(Player player) {
		broadcastMessage(ServerMessages.genTurnOfPlayerString(player.playerID));
		if (player instanceof ComputerPlayer) {
			processMove(null, ((ComputerPlayer) player).determineMove(board));
		}
	}
	
	/**
	 * Processes a move determined by the given coordinates. Notifies players of game endings. 
	 * Handles invalid moves.
	 * @param handler ClientHandler caller, null for a move by a ComputerPlayer
	 * @param coords Coordinates of the move
	 */
	//@ requires handler != null;
	//@ requires coords != null && board.isValidMove(coords.getX(), coords.getY());
	public void processMove(ClientHandler handler, TowerCoordinates coords) {
		synchronized (this) {
			if ((handler == null || getHandler(currentPlayer) == handler) && 
					board.isValidMove(coords.x, coords.y)) {
				//Caller is a ComputerPlayer or the correct human player, move is valid
				try {
					board.makeMove(coords.x, coords.y, currentPlayer.playerID);
					broadcastMessage(ServerMessages.genNotifyMoveString(currentPlayer.playerID, 
							coords.x, coords.y));
					if (board.hasWon(coords.x, coords.y)) {
						broadcastMessage(ServerMessages.genNotifyWinString(currentPlayer.playerID));
						shutdown();
					} else if (board.isFull()) {
						broadcastMessage(ServerMessages.genNotifyDrawString());
						shutdown();
					} else {
						if (!exit) {
							nextPlayer();
							requestMove(currentPlayer);
						}
					}
				} catch (IllegalCoordinatesException e) {
					//Something goes awfully wrong
					view.printMessage(e.getMessage());
					shutdown();
				}
			} else if (currentPlayer instanceof ComputerPlayer) {
				//Caller is a ComputerPlayer and sends an illegal move
				broadcastMessage(ServerMessages.genNotifyDisconnectString(currentPlayer.playerID));
				shutdown();
			} else if (handler != null && getHandler(currentPlayer) != handler) {
				//Caller is not a ComputerPlayer and sends data while it shouldn't
				handler.bullshitReceived();
				handler.sendMessage(ServerMessages.genErrorInvalidCommandString());
			} else {
				//Caller is current player and sends an illegal move
				handler.bullshitReceived();
				handler.sendMessage(ServerMessages.genErrorInvalidMoveString());
			}
		}
	}
	
	/**
	 * Drops the given player and replaces it with a ComputerPlayer with smart strategy with the 
	 * same ID. Anti-cheat measure for rage quits.
	 * @param player Player to replace
	 */
	//@ requires client != null;
	public synchronized void replaceClient(ClientHandler client) {
		Player toReplace = null;
		synchronized (handlerMap) {
			for (Map.Entry<Player, ClientHandler> handlerMapEntry : handlerMap.entrySet()) {
				if (handlerMapEntry.getValue() == client) {
					toReplace = handlerMapEntry.getKey();
				}
			}
		}
		// Synchronized to ensure handlerMap is locked shutdown or broadcastMessage try to iterate 
		// over it
		synchronized (handlerMap) {
			if (toReplace != null) {
				ComputerPlayer compPlayer = new ComputerPlayer(new SmartStrategy(), 
					toReplace.playerID);
				players.add(players.indexOf(toReplace), compPlayer);
				players.remove(toReplace);
				handlerMap.remove(toReplace);
				if (handlerMap.size() == 0) {
					shutdown();
				} else if (currentPlayer == toReplace) {
					currentPlayer = compPlayer;
					processMove(null, compPlayer.determineMove(board));
				}
			}
		}
	}
	
	/**
	 * The method returns if the game expects input from a given Clienthandler.
	 * @param handler Clienthandler that should be tested.
	 * @return if the handler is the current player or not.
	 */
	//@ requires handler != null;
	/*pure*/ public boolean expectsHandlerInput(ClientHandler handler) {
		return handlerMap.get(currentPlayer) == handler;
	}
	
	/**
	 * Gets the handler belonging to a player.
	 * @param player A player
	 * @return Its handler, null if ComputerPlayer
	 */
	//@ requires player != null;
	/*nullable*/ /*pure*/ private ClientHandler getHandler(Player player) {
		return handlerMap.get(player);
	}
	
	/**
	 * Sends a message through all ClientHandlers.
	 * @param message The message to broadcast.
	 */
	//@ requires message != null;
	private void broadcastMessage(String message) {
		// Synchronized to ensure handlerMap is locked should replaceClient be called while this 
		// method is being executed
		synchronized (handlerMap) {
			for (ClientHandler handler : handlerMap.values()) {
				handler.sendMessage(message);
			}
		}
	}
	
	/**
	 * The method shuts down the game with the handlers.
	 */
	public void shutdown() {
		exit = true;
		String toPrint = "Shutting down game with handlers to";
		// Synchronized to ensure handlerMap is locked should replaceClient be called while this 
		// method is being executed
		synchronized (handlerMap) {
			for (ClientHandler handler : handlerMap.values()) {
				handler.shutdown();
				toPrint = toPrint + " " + handler.toString();
			}
		}
		view.printMessage(toPrint);
	}
}

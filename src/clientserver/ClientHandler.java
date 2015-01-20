package clientserver;

import game.Board;
import game.Disc;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;
import java.util.Arrays;

// TODO: Auto-generated Javadoc
/**
 * The clientHandler that reads all the input from the clients and send messages
 * from the server to the clients.
 * 
 * @author Sven Konings en Michael Koopman
 * @version 1.0 $
 */
public class ClientHandler extends Thread {
	/** The Constant WIN. */
	public static final String WIN = "WIN";

	/** The Constant DRAW. */
	public static final String DRAW = "DRAW";

	/** The Constant DISCONECT. */
	public static final String DISCONNECT = "DISCONNECT";
	/**
	 * The Server for this ClientHandler.
	 */
	private Server server;

	/**
	 * The Socket this ClientHandler will use to connect to the Client.
	 */
	private Socket sock;

	/**
	 * The BufferedReader used to receive packets from the Client.
	 */
	private BufferedReader in;

	/**
	 * The BufferedWriter used to send packets to the Client.
	 */
	private BufferedWriter out;

	/**
	 * The name of the Client this ClientHandler is associated with.
	 */
	private String clientName;

	/**
	 * The list of the features of the Client this ClientHandler is associated
	 * with.
	 */
	private String[] features;

	/**
	 * The playerNumber of this client when this client is in a game.
	 */
	private int playerNumber;

	/**
	 * The name of the client this client playing against when this client is in
	 * a game.
	 */
	private String opponentName;

	/**
	 * The board this client is playing on when it is in a game.
	 */
	private Board board;

	/**
	 * A boolean indicating wether the server has requested a move.
	 */
	private boolean move;

	/**
	 * A loop variable used to check whether to keep looping or not.
	 */
	private boolean loop;

	/*@ private invariant server != null;
		private invariant sock != null;
		private invariant in != null;
		private invariant out != null;
		private invariant playerNumber == -1 || playerNumber == 0 || playerNumber == 1;
	 */

	/**
	 * Constructs a ClientHandler object. Initialises both the BufferedReader
	 * and the BufferedWriter.
	 * 
	 *
	 * @param serverArg
	 *            the server arg
	 * @param sockArg
	 *            the sock arg
	 * @throws IOException
	 *             Signals that an I/O exception has occurred.
	 */
	//@ requires server != null && sock != null;
	public ClientHandler(Server server, Socket sock) throws IOException {
		this.server = server;
		this.sock = sock;
		this.in = new BufferedReader(new InputStreamReader(
				sock.getInputStream()));
		this.out = new BufferedWriter(new OutputStreamWriter(
				sock.getOutputStream()));
		this.clientName = null;
		this.features = null;
		this.playerNumber = -1;
		this.opponentName = null;
		this.board = null;
		this.move = false;
		this.loop = true;
	}

	/**
	 * This method takes care of sending messages from the Client. Every message
	 * that is received, is preprended with the name of the Client, and the new
	 * message is offered to the Server for broadcasting. If an IOException is
	 * thrown while reading the message or the message is null and a
	 * NullPointerException is thrown, the method concludes that the socket
	 * connection is broken and shutdown() will be called.
	 */
	public void run() {
		while (loop) {
			String line = "";
			String[] command = null;
			try {
				line = in.readLine();
				command = line.split("\\s+");
			} catch (IOException | NullPointerException e) {
				if (loop) {
					shutdown();
				}
				break;
			}
			switch (command[0]) {
			case Client.CONNECT:
				connectChecks(command);
				break;
			case Client.QUIT:
				shutdown();
				break;
			case Client.INVITE:
				inviteChecks(command);
				break;
			case Client.ACCEPT_INVITE:
				acceptChecks(command);
				break;
			case Client.DECLINE_INVITE:
				declineChecks(command);
				break;
			case Client.MOVE:
				moveChecks(command);
				break;
			case Client.CHAT:
				chatChecks(command);
				break;
			case Client.REQUEST_BOARD:
				requestBoardChecks();
				break;
			case Client.REQUEST_LOBBY:
				requestLobbyChecks();
				break;
			case Client.REQUEST_LEADERBOARD:
				sendMessage(Server.ERROR + " Not implemented");
				// TODO: leaderbords opslaan
				break;
			default:
				sendMessage(Server.ERROR + " Invalid command");
				break;
			}

		}
	}

	/**
	 * This method can be used to send a message over the socket connection to
	 * the Client. If the writing of a message fails, the method concludes that
	 * the socket connection has been lost and shutdown() is called.
	 *
	 * @param msg
	 *            the message
	 */
	//@ requires msg != null;
	public synchronized void sendMessage(String msg) {
		String[] command = msg.split("\\s+");
		switch (command[0]) {
		case Server.GAME_START:
			startGame(command);
			break;
		case Server.GAME_END:
			endGame();
			break;
		case Server.REQUEST_MOVE:
			move = true;
			break;
		}
		try {
			out.write(msg);
			out.newLine();
			out.flush();
		} catch (IOException e) {
			if (loop) {
				shutdown();
			}
		}
		server.print("ClientHandler to " + clientName + ": " + msg);
	}

	/**
	 * returns the name of the client.
	 *
	 * @return the name of the client
	 */
	/*@ pure */public String getClientName() {
		return clientName;
	}

	/**
	 * returns the features of the client.
	 *
	 * @return the features of the client
	 */
	/*@ pure */public String[] getClientFeatures() {
		return features;
	}

	/**
	 * returns wheter this cliens has connected.
	 *
	 * @return true if the client has a name
	 */
	/*@ pure */public boolean connected() {
		return clientName != null;
	}

	/**
	 * returns wheter the client is playing a game.
	 *
	 * @return true if there is a board
	 */
	/*@ pure */public boolean inGame() {
		return board != null;
	}

	/**
	 * Sets the board of this client.
	 *
	 * @param b
	 *            the new board
	 */
	//@ requires connected();
	//@ requires b != null;
	public void setBoard(Board b) {
		board = b;
	}

	/**
	 * Checks if the client has send a command with valid arguments and with a
	 * valid name. If this is the case connect will be called to conect the
	 * client
	 *
	 * @param command
	 *            the command send by the client
	 */
	//@ requires command[0].equals(Client.CONNECT);
	private void connectChecks(String[] command) {
		if (command.length < 2) {
			sendMessage(Server.ERROR + " Invalid arguments");
		} else if (command[1].length() > 15) {
			sendMessage(Server.ERROR + " Name too long");
		} else if (server.nameExists(command[1])) {
			sendMessage(Server.ERROR + " Name in use");
		} else {
			connect(command);
		}
	}

	/**
	 * Connects the clients by assigning the name specified in the command and
	 * storing the features. Then it send an ACCEPT_CONNECT with the features of
	 * the client
	 *
	 * @param command
	 *            the command send by the client
	 */
	/*@ requires command.length >= 2;
		requires command[1].length <= 15;
		requires server.nameExists(command[1]);
		ensures connected();
		ensures command.length > 2 ==> features != null;
	 */
	private void connect(String[] command) {
		clientName = command[1];
		if (command.length > 2) {
			// TODO: controleren valid features
			features = Arrays.copyOfRange(command, 2, command.length - 1);
		}
		// TODO: onze features sturen
		sendMessage(Server.ACCEPT_CONNECT
				+ " Feature array gescheiden met spaties");
		server.print("ClientHandler: " + clientName + " has joined");
		server.broadcastLobby();
	}

	/**
	 * Checks if the client is connected, if the client send a command with
	 * valid arguments, if the opponent exists, if neither player is in a game
	 * and checks wether there is no invite between both player. If this is the
	 * case invite will be called and an invite will be send to the opponent
	 * specified in the command. You can invite and play against yourself.
	 *
	 * @param command
	 *            the command send by the client
	 */
	//@ requires command[0].equals(Client.INVITE);
	private void inviteChecks(String[] command) {
		if (!connected()) {
			sendMessage(Server.ERROR + " You have to connect first");
		} else if (command.length < 2) {
			sendMessage(Server.ERROR + " Invalid arguments");
		} else if (!server.nameExists(command[1])) {
			sendMessage(Server.ERROR + " Name doesn't exist");
		} else if (inGame()) {
			sendMessage(Server.ERROR + " You are already in a game");
		} else if (server.inGame(command[1])) {
			sendMessage(Server.ERROR + " This client is already in a game");
		} else if (server.isInvited(clientName, command[1])) {
			sendMessage(Server.ERROR + " Already invited this client");
		} else if (server.isInvited(command[1], clientName)) {
			sendMessage(Server.ERROR + " This client already invited you");
		} else {
			invite(command);
		}
	}

	/**
	 * Invites the player specified in the command and tries to read the board
	 * size if specified. the invite will be saved on the server.
	 *
	 * @param command
	 *            the command send by the client
	 */
	/*@ requires connected();
		requires command.length >= 2;
		requires server.nameExists(command[1]);
		requires !inGame();
		requires !server.inGame(command[1]);
		requires !server.isInvited(clientName, command[1]);
		requires !server.isInvited(command[1], clientName);
		ensures server.isInvited(clientName, command[1]);
	 */
	private void invite(String[] command) {
		int boardX = 7;
		int boardY = 6;
		if (command.length >= 4) {
			try {
				boardX = Integer.parseInt(command[2]);
				boardY = Integer.parseInt(command[3]);
			} catch (NumberFormatException e) {
				sendMessage(Server.ERROR
						+ " could not parse boardsize, using default");
				boardX = 7;
				boardY = 6;
			}
			server.sendMessage(command[1], Server.INVITE + " " + clientName
					+ " " + boardX + " " + boardY);
		} else {
			server.sendMessage(command[1], Server.INVITE + " " + clientName);
		}
		server.addInvite(clientName, command[1], boardX, boardY);
	}

	/**
	 * Checks if the client is connected, if the client send a command with
	 * valid arguments, if the opponent exists and if the opponent specified in
	 * the command send an invite to this player. If this is the case accept
	 * will be called to accept the invite.
	 *
	 * @param command
	 *            the command send by the client
	 */
	//@ requires command[0].equals(Client.ACCEPT_INVITE);
	private void acceptChecks(String[] command) {
		if (!connected()) {
			sendMessage(Server.ERROR + " You have to connect first");
		} else if (command.length != 2) {
			sendMessage(Server.ERROR + " Invalid arguments");
		} else if (!server.nameExists(command[1])) {
			sendMessage(Server.ERROR + " Name doesn't exist");
		} else if (!server.isInvited(command[1], clientName)) {
			sendMessage(Server.ERROR + " Not invited by this client");
		} else {
			accept(command);
		}
	}

	/**
	 * Accepts the invite, creates a board with the size specified in the invite
	 * and announces the start of the game to this client and the specified
	 * opponent.
	 *
	 * @param command
	 *            the command send by the client
	 */
	/*@ requires connected();
		requires command.length == 2;
		requires server.nameExists(command[1]);
		requires server.isInvited(command[1], clientName);
	 */
	private void accept(String[] command) {
		// TODO: extras verzenden (spectators?)
		server.generateBoard(command[1], clientName);
		sendMessage(Server.GAME_START + " " + clientName + " " + command[1]);
		server.sendMessage(command[1], Server.GAME_START + " " + clientName
				+ " " + command[1]);
		sendMessage(Server.REQUEST_MOVE);
	}

	/**
	 * Checks if the client is connected, if the client send a command with
	 * valid arguments, if the opponent exists and if the opponent specified in
	 * the command send an invite to this player. If this is the case decline
	 * will be called to decline the invite.
	 *
	 * @param command
	 *            the command send by the client
	 */
	//@ requires command[0].equals(Client.DECLINE_INVITE);
	private void declineChecks(String[] command) {
		if (!connected()) {
			sendMessage(Server.ERROR + " You have to connect first");
		} else if (command.length != 2) {
			sendMessage(Server.ERROR + " Invalid arguments");
		} else if (!server.nameExists(command[1])) {
			sendMessage(Server.ERROR + " Name doesn't exist");
		} else if (!server.isInvited(command[1], clientName)) {
			sendMessage(Server.ERROR + " Not invited by this client");
		} else {
			decline(command);
		}
	}

	/**
	 * Declines the invite, send a message to the opponent and deletes it from
	 * the server.
	 *
	 * @param command
	 *            the command send by the client
	 */
	/*@ requires connected;
		requires command.length == 2;
		requires server.nameExists(command[1]);
		requires server.isInvited(command[1], clientName);
		ensures !server.isInvited(command[1], clientName);
	 */
	private void decline(String[] command) {
		//TODO: decline je eigen invite
		server.removeInvite(command[1], clientName);
		server.sendMessage(command[1], Server.ERROR + " " + clientName
				+ " Declined your invite");
	}

	/**
	 * Checks if the client is connected, if the client is in game and if it's
	 * the client's turn to move, if this is the case it calls validMove to
	 * check if the move is valid.
	 *
	 * @param command
	 *            the command send by the client
	 */
	//@ requires command[0].equals(Client.MOVE);
	private void moveChecks(String[] command) {
		// TODO: game met meer dan 2 players of spectators
		if (!connected()) {
			sendMessage(Server.ERROR + " You have to connect first");
		} else if (!inGame()) {
			sendMessage(Server.ERROR + " You aren't in a game");
		} else if (!move) {
			sendMessage(Server.ERROR + " It's not your turn to move");
		} else {
			validMove(command);
		}
	}

	/**
	 * Checks if the client send a command with valid arguments, tries to parse
	 * the column specified in the command, checks if the column is a valid
	 * column and if it isn't full. If one of these things fail it sends an
	 * error and a new move request, otherwise it will call move to do the move.
	 *
	 * @param command
	 *            the command send by the client
	 */
	private void validMove(String[] command) {
		move = false;
		if (command.length != 2) {
			sendMessage(Server.ERROR + " Invalid arguments");
			sendMessage(Server.REQUEST_MOVE);
		} else {
			int col = -1;
			try {
				col = Integer.parseInt(command[1]);
			} catch (NumberFormatException e) {
				sendMessage(Server.ERROR + " Can't parse move");
				sendMessage(Server.REQUEST_MOVE);
			}
			if (!board.isField(col)) {
				sendMessage(Server.ERROR + " That column doesn't exist");
				sendMessage(Server.REQUEST_MOVE);
			} else if (!board.isEmptyField(col)) {
				sendMessage(Server.ERROR + " That column is full");
				sendMessage(Server.REQUEST_MOVE);
			} else {
				move(col);
			}
		}
	}

	/**
	 * Does the move on the board, sends the move to the clients in the game and
	 * checks if the game is over. If it isn't it sends an request to the
	 * opponent, otherwise it will send the result of the game.
	 *
	 * @param col
	 *            the col
	 */
	/*@ requires connected();
		requires opponentName != null;
		requires playerNumber == 0 || playerNumber == 1;
		requires inGame();
		requires board.isField(col);
		requires board.isEmptyField(col);
	 */
	private void move(int col) {
		if (playerNumber == 0) {
			board.insertDisc(col, Disc.YELLOW);
		} else if (playerNumber == 1) {
			board.insertDisc(col, Disc.RED);
		}
		sendMessage(Server.MOVE_OK + " " + playerNumber + " " + col + " "
				+ clientName);
		server.sendMessage(opponentName, Server.MOVE_OK + " " + playerNumber
				+ " " + col + " " + clientName);
		if (!board.gameOver()) {
			server.sendMessage(opponentName, Server.REQUEST_MOVE);
		} else if (board.hasWinner()) {
			// TODO: game end final strings
			server.sendMessage(opponentName, Server.GAME_END + " " + WIN + " "
					+ clientName);
			sendMessage(Server.GAME_END + " " + WIN + " " + clientName);
		} else {
			server.sendMessage(opponentName, Server.GAME_END + " " + DRAW);
			sendMessage(Server.GAME_END + " " + DRAW);
		}
	}

	/**
	 * Checks if the client is connected and if the command contains a message,
	 * if this is the case it calls chat to broadcast the message.
	 *
	 * @param command
	 *            the command send by the client
	 */
	//@ requires command[0].equals(Client.CHAT);
	private void chatChecks(String[] command) {
		if (!connected()) {
			sendMessage(Server.ERROR + " You have to connect first");
		} else if (command.length < 2) {
			sendMessage(Server.ERROR + " Invalid arguments");
		} else {
			chat(command);
		}
	}

	/**
	 * Broadcasts the message to all connected clients.
	 *
	 * @param command
	 *            the command send by the client
	 */
	//@ requires connected();
	//@ requires command.length >= 2;
	private void chat(String[] command) {
		// TODO: line sturen zonder eerste woord
		String chat = "";
		for (int i = 1; i < command.length; i++) {
			chat += " " + command[i];
		}
		server.broadcast(Server.CHAT + " " + clientName + ":" + chat);
	}

	/**
	 * Checks if the client is connected and if the client is in game. If this
	 * is the case it calls requestBoard to send the board.
	 */
	private void requestBoardChecks() {
		if (!connected()) {
			sendMessage(Server.ERROR + " You have to connect first");
		} else if (!inGame()) {
			sendMessage(Server.ERROR + " You aren't in a game");
		} else {
			requestBoard();
		}
	}

	/**
	 * Sends the board to the client.
	 */
	//@ requires connected();
	//@ requires inGame();
	private void requestBoard() {
		sendMessage(Server.BOARD + " " + board.toProtocol());
	}

	/**
	 * Checks if the client is connected. If this is the case it calls
	 * requestLobby to send the lobby.
	 */
	private void requestLobbyChecks() {
		if (!connected()) {
			sendMessage(Server.ERROR + " You have to connect first");
		} else {
			requestLobby();
		}
	}

	/**
	 * Sends the lobby to the client.
	 */
	//@ requires connected();
	private void requestLobby() {
		sendMessage(Server.LOBBY + server.getLobby());
	}

	/**
	 * Starts a game and sets the playerNumber and opponentName belonging to the
	 * client. Also removes all the invites of the client and broadcasts the
	 * lobby because the client just left the lobby.
	 *
	 * @param command
	 *            the command send by the client
	 */
	//@ ensures playerNumber == 0 || playerNumber == 1;
	//@ ensures opponentName != null;
	private void startGame(String[] command) {
		// TODO: game maken inplaats bord
		server.removeInvite(clientName);
		if (clientName.equals(command[1])) {
			playerNumber = 0;
			opponentName = command[2];
		} else {
			playerNumber = 1;
			opponentName = command[1];
		}
		server.broadcastLobby();
	}

	/**
	 * End s the game, resets the values belonging to the game and broadcasts
	 * the lobby because this client just joined the lobb again.
	 */
	//@ ensures playerNumber == -1;
	//@ ensures opponentName == null;
	//@ ensures !inGame();
	private void endGame() {
		playerNumber = -1;
		board = null;
		opponentName = null;
		server.broadcastLobby();
	}

	/**
	 * This ClientHandler signs off from the Server and subsequently sends a
	 * last broadcast to the Server to inform that the Client is no longer
	 * participati ng in the lobby.
	 */
	//@ ensures loop == false;
	private void shutdown() {
		// TODO: clients moeten kunnen reconnecten na dc
		this.loop = false;
		server.removeInvite(clientName);
		server.removeHandler(this);
		if (inGame()) {
			server.sendMessage(opponentName, Server.GAME_END + " " + DISCONNECT);
		} else if (clientName != null) {
			server.broadcastLobby();
		}
		server.print("ClientHandler: " + clientName + " has left");
		try {
			sock.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
}

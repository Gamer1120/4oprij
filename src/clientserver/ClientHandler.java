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
 * ClientHandler.
 * 
 * @author Theo Ruys
 * @version 2005.02.21
 */
public class ClientHandler extends Thread {

	/**
	 * The <code>Server</code> for this <code>ClientHandler</code>.
	 */
	private Server server;

	/**
	 * The <code>Socket</code> this <code>ClientHandler</code> will use to
	 * connect to the <code>Client</code>.
	 */
	private Socket sock;

	/**
	 * The <code>BufferedReader</code> used to receive packets from the
	 * <code>Client</code>.
	 */
	private BufferedReader in;

	/**
	 * The <code>BufferedWriter</code> used to send packets to the
	 * <code>Client</code>.
	 */
	private BufferedWriter out;

	/**
	 * The name of the <code>Client</code> this <code>ClientHandler</code> is
	 * associated with.
	 */
	private String clientName;

	/**
	 * The list of the features of the <code>Client</code> this
	 * <code>ClientHandler</code> is associated with.
	 */
	private String[] features;

	/** TO BE REMOVED. */
	private int playerNumber;

	/** TO BE REMOVED. */
	private String opponentName;

	/** TO BE CHANGED TO GAME. */
	private Board board;

	/** The move. */
	private boolean move;

	/**
	 * A loop variable used to check whether to keep looping or not in a certain
	 * method.
	 */
	private boolean loop;

	// @requires server != null && sock != null;
	/**
	 * Constructs a <code>ClientHandler</code> object. Initialises both the
	 * <code>BufferedReader</code> and the <code>BufferedWriter</code>.
	 * 
	 *
	 * @param serverArg
	 *            the server arg
	 * @param sockArg
	 *            the sock arg
	 * @throws IOException
	 *             Signals that an I/O exception has occurred.
	 */
	public ClientHandler(Server serverArg, Socket sockArg) throws IOException {
		this.server = serverArg;
		this.sock = sockArg;
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
	 * thrown while reading the message, the method concludes that the socket
	 * connection is broken and shutdown() will be called.
	 */
	public void run() {
		while (loop) {
			String line = "";
			try {
				line = in.readLine();
			} catch (IOException | NullPointerException e) {
				if (loop) {
					shutdown();
				}
			}
			String[] command = line.split("\\s+");
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
				// TODO: zelf bord bijhouden om op te sturen
				break;
			case Client.REQUEST_LOBBY:
				sendMessage(Server.LOBBY + server.getLobby());
				break;
			case Client.REQUEST_LEADERBOARD:
				// TODO: leaderbords opslaan
				break;
			default:
				sendMessage(Server.ERROR + " Invalid command");
			}

		}
	}

	/**
	 * This method can be used to send a message over the socket connection to
	 * the Client. If the writing of a message fails, the method concludes that
	 * the socket connection has been lost and shutdown() is called.
	 *
	 * @param msg
	 *            the msg
	 */
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
			server.print("ClientHandler to " + clientName + ": " + msg);
		} catch (IOException | NullPointerException e) {
			if (loop) {
				shutdown();
			}
		}
	}

	/**
	 * returns the name of the client.
	 *
	 * @return the name of the client
	 */
	public String getClientName() {
		return clientName;
	}

	/**
	 * returns the features of the client.
	 *
	 * @return the features of the client
	 */
	public String[] getClientFeatures() {
		return features;
	}

	/**
	 * returns wheter the client is playing a game.
	 *
	 * @return true, if successful
	 */
	public boolean inGame() {
		return board != null;
	}

	/**
	 * Sets the board of this client.
	 *
	 * @param b
	 *            the new board
	 */
	public void setBoard(Board b) {
		board = b;
	}

	/**
	 * Connect.
	 *
	 * @param command
	 *            the command
	 */
	private void connectChecks(String[] command) {
		// TODO: controleren op naam lengte
		if (command.length < 2) {
			sendMessage(Server.ERROR + " Invalid arguments");
		} else if (server.nameExists(command[1])) {
			sendMessage(Server.ERROR + " Name in use");
		} else if (command[1].length() > 15) {
			sendMessage(Server.ERROR + " Name too long");
		} else {
			connect(command);
		}
	}

	/**
	 * Connect.
	 *
	 * @param command
	 *            the command
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
		server.broadcastLobby();
		server.print("ClientHandler: " + clientName + " has joined");
	}

	// You can invite and play against yourself
	/**
	 * Invite.
	 *
	 * @param command
	 *            the command
	 */
	private void inviteChecks(String[] command) {
		if (command.length < 2) {
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
	 * Invite.
	 *
	 * @param command
	 *            the command
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
	 * Accept.
	 *
	 * @param command
	 *            the command
	 */
	private void acceptChecks(String[] command) {
		if (command.length != 2) {
			sendMessage(Server.ERROR + " Invalid arguments");
		} else if (!server.isInvited(command[1], clientName)) {
			sendMessage(Server.ERROR + " Not invited by this client");
		} else {
			accept(command);
		}
	}

	/**
	 * Accept.
	 *
	 * @param command
	 *            the command
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
	 * Decline.
	 *
	 * @param command
	 *            the command
	 */
	private void declineChecks(String[] command) {
		if (command.length != 2) {
			sendMessage(Server.ERROR + " Invalid arguments");
		} else if (!server.isInvited(command[1], clientName)) {
			sendMessage(Server.ERROR + " Not invited by this client");
		} else {
			decline(command);
		}
	}

	/**
	 * Decline.
	 *
	 * @param command
	 *            the command
	 */
	private void decline(String[] command) {
		server.removeInvite(command[1], clientName);
		server.sendMessage(command[1], Server.ERROR + " Invite declined");
	}

	/**
	 * Move.
	 *
	 * @param command
	 *            the command
	 */
	private void moveChecks(String[] command) {
		// TODO: mogeljk game met players en spectators?
		// TODO: check wie aan de beurt is, mogelijk bij request
		// TODO: zelf bord bijhouden voor nummer en move ok checken
		if (!inGame()) {
			sendMessage(Server.ERROR + " You aren't in a game");
		} else if (!move) {
			sendMessage(Server.ERROR + " It's not your turn to move");
		} else {
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
	}

	/**
	 * Move.
	 *
	 * @param col
	 *            the col
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
			//TODO: game end finals
			server.sendMessage(opponentName, Server.GAME_END + " " + "WIN"
					+ " " + clientName);
			sendMessage(Server.GAME_END + " " + "WIN" + " " + clientName);
		} else {
			server.sendMessage(opponentName, Server.GAME_END + " " + "DRAW");
			sendMessage(Server.GAME_END + " " + "DRAW");
		}
	}

	/**
	 * Chat.
	 *
	 * @param command
	 *            the command
	 */
	private void chatChecks(String[] command) {
		if (command.length < 2) {
			sendMessage(Server.ERROR + " Invalid arguments");
		} else {
			chat(command);
		}
	}

	/**
	 * Chat.
	 *
	 * @param command
	 *            the command
	 */
	private void chat(String[] command) {
		String chat = "";
		for (int i = 1; i < command.length; i++) {
			chat += " " + command[i];
		}
		server.broadcast(Server.CHAT + " " + clientName + ":" + chat);
	}

	/**
	 * Start game.
	 *
	 * @param command
	 *            the command
	 */
	private void startGame(String[] command) {
		// TODO: echte game maken
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
	 * End game.
	 */
	private void endGame() {
		playerNumber = -1;
		board = null;
		opponentName = null;
	}

	/**
	 * This ClientHandler signs off from the Server and subsequently sends a
	 * last broadcast to the Server to inform that the Client is no longer
	 * participating in the lobby.
	 */
	private void shutdown() {
		// TODO: clients moeten kunnen reconnecten na dc
		this.loop = false;
		server.removeInvite(clientName);
		server.removeHandler(this);
		if (inGame()) {
			server.sendMessage(opponentName, Server.GAME_END + " "
					+ "DISCONNECT");
		} else {
			server.broadcastLobby();
		}
		server.print("ClientHandler: " + clientName + " has left");
		this.server = null;
		this.sock = null;
		this.in = null;
		this.out = null;
		this.clientName = null;
		this.features = null;
		this.playerNumber = -1;
		this.opponentName = null;
		this.board = null;
		this.move = false;
	}
} // end of class ClientHandler

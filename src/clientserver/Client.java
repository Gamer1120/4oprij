package clientserver;

import game.Board;
import game.Disc;
import game.HumanPlayer;
import game.ComputerPlayer;
import game.NaiveStrategy;
import game.Player;
import game.SmartStrategy;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.InetAddress;
import java.net.Socket;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

/**
 * Client program for the Connect4 according to the protocol of the TI-2 group.<br>
 * <br>
 * Programming Project Connect4 Module 2 Softwaresystems 2014-2015 <br>
 * 
 * @author Michael Koopman s1401335 and Sven Konings s1534130
 */
public class Client {
	// The protocol, as discussed in our TI-2 group. For further explanation,
	// you can look at the protocol documentation.
	public static final String CONNECT = "CONNECT";
	public static final String QUIT = "QUIT";
	public static final String INVITE = "INVITE";
	public static final String ACCEPT_INVITE = "ACCEPT";
	public static final String DECLINE_INVITE = "DECLINE";
	public static final String MOVE = "MOVE";
	public static final String CHAT = "CHAT";
	public static final String REQUEST_BOARD = "REQUEST";
	public static final String REQUEST_LOBBY = "LOBBY";
	public static final String REQUEST_LEADERBOARD = "LEADERBOARD";
	public static final String ERROR = "ERROR";
	public static final String PING = "PING";
	// END OF PROTOCOL
	private static final String CLIENT_FEATURES = Features.CHAT + " "
			+ Features.CUSTOM_BOARD_SIZE + " " + Features.LEADERBOARD;
	public String firstPlayer;
	public String secondPlayer;

	/**
	 * The name of this Client.
	 */
	private String clientName;

	/**
	 * The User Interface of this Client.
	 */
	private ClientTUI mui;
	/**
	 * The Socket of this Client.
	 */
	private Socket sock;
	/**
	 * The BufferedReader that will be used to communicate over the Socket.
	 */
	private BufferedReader in;
	/**
	 * The BufferedWriter that will be used to communicate over the Socket.
	 */
	private BufferedWriter out;
	/**
	 * While this boolean is true, it makes sure that commands are continuously
	 * read from the BufferedReader.
	 */
	private boolean loop;
	/**
	 * A variable to test if a Player is in-game. If they are, they won't
	 * receive any invite messages.
	 */
	public boolean isIngame;
	/**
	 * The Board this Client uses for determining their move.
	 */
	private Board board;
	/**
	 * An integer to determine which Player's turn it is.
	 */
	private String currPlayer;
	/**
	 * A boolean to determine whether this Client is connected.
	 */
	private boolean isConnected;
	/**
	 * The Player this Client is.
	 */
	private Player localPlayer;
	/**
	 * If the Client requests the Board from the server, it's saved here that it
	 * has already been requested, so it's not requested for a second time.
	 */
	private boolean requestedBoard;
	/**
	 * A Map of invites this Client is invited by. This map gets emptied every
	 * time a Game starts.
	 */
	private Map<String, Integer[]> invitedBy;
	/**
	 * A Map of invited this Client sent. This map gets emptied every time a
	 * Game starts.
	 */
	private Map<String, Integer[]> invited;

	private InetAddress host;

	private int port;

	/*@	private invariant sock != null;
	 	private invariant mui != null;
	 	private invariant in != null;
	 	private invariant out != null;
	  	private invariant invited != null;
	  	private invariant invitedBy != null;
	  	private invariant localPlayer != null;
	 */

	/**
	 * Constructs a Client object and tries to make a Socket connection
	 * 
	 * @param host
	 *            The IP-adress of this Client
	 * @param port
	 *            The port of this Client
	 * @param muiArg
	 *            The MessageUI for this Client
	 * @param localPlayer
	 *            The Player Object to use for this Client
	 */
	/*@ requires host != null;
	 	requires port >= 1 & port <= 65535;
	 	requires muiArg != null;
	 	requires localPlayer != null;
	 */
	public Client(ClientTUI muiArg) {
		this.isConnected = false;
		this.invited = new HashMap<String, Integer[]>();
		this.invitedBy = new HashMap<String, Integer[]>();
		this.loop = true;

		this.mui = muiArg;
		this.clientName = mui.askName();
		this.localPlayer = null;
		while (localPlayer == null) {
			setUpPlayer();
		}
		this.host = null;
		while (host == null) {
			setUpIP();
		}
		this.port = -1;
		while (port == -1) {
			setUpPort();
		}
		mui.setClient(this);
		try {
			this.sock = new Socket(host, port);
			this.in = new BufferedReader(new InputStreamReader(
					sock.getInputStream()));
			this.out = new BufferedWriter(new OutputStreamWriter(
					sock.getOutputStream()));
		} catch (IOException e) {
			// TODO Ask again for IP and port
			e.printStackTrace();
		}
		this.isIngame = false;
		this.requestedBoard = false;
		sendMessage(CONNECT + " " + getClientName() + " " + CLIENT_FEATURES);
		readInput();

	}

	/**
	 * This method reads the messages in the InputStream. Then, it decides which
	 * command was sent, and executes this command by calling the method created
	 * for it.
	 */
	public void readInput() {
		while (loop) {
			String line = "";
			try {
				line = in.readLine();
			} catch (IOException | NullPointerException e) {
				shutdown();
			}
			mui.addMessage("[SERVER]" + line);
			String[] serverMessage = line.split("\\s+");
			switch (serverMessage[0]) {
			case Server.ACCEPT_CONNECT:
				isConnected = true;
				connect(serverMessage);
				mui.start();
				break;
			case Server.LOBBY:
				lobby(serverMessage);
				break;
			case Server.INVITE:
				invite(serverMessage);
				break;
			case Server.DECLINE_INVITE:
				declineInvite(serverMessage);
				break;
			case Server.GAME_START:
				gameStart(serverMessage);
				break;
			case Server.GAME_END:
				gameEnd(serverMessage);
				break;
			case Server.REQUEST_MOVE:
				requestMove(serverMessage);
				break;
			case Server.MOVE_OK:
				moveOK(serverMessage);
				break;
			case Server.ERROR:
				//TODO: Zet dit netjes neer.
				mui.addMessage("[ERROR]" + line.split(" ", 2)[1]);
				if (!isConnected) {
					mui.askName();
				}
				break;
			case Server.BOARD:
				board = toBoard(line);
				notifyAll();
				break;
			case Server.CHAT:
				mui.addMessage("[CHAT]" + line.split(" ", 2)[1]);
				break;
			case Server.LEADERBOARD:
				showLeaderBoard(serverMessage);
				break;
			case Server.PONG:
				mui.addMessage("[PING]Pong!");
				break;
			default:
				sendMessage(ERROR + " " + serverMessage[0]
						+ " Unknown command.");
				break;
			}
		}
	}

	/**
	 * This method accepts the Server.CONNECT packet sent by the Server. When
	 * this method is called, it prints that a connection has been established
	 * with the Server, as well as the IP adress and port of the Server. After
	 * this, it lists the features the Server has.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	//@	requires serverMessage[0].equals(Server.ACCEPT_CONNECT);
	private void connect(String[] serverMessage) {
		mui.addMessage("[CONNECT]Successfully established connection to server: "
				// IP of the server
				+ sock.getRemoteSocketAddress().toString());
		mui.addMessage("[FEATURES]The features of this server are:"
				+ arrayToLine(serverMessage));
	}

	/**
	 * This method accepts the Server.LOBBY packet sent by the Server. When this
	 * method is called, it shows the Client the other Clients that are
	 * currently in the lobby.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	//@ requires serverMessage[0].equals(Server.LOBBY);
	private void lobby(String[] serverMessage) {
		mui.addMessage("[LOBBY]The people that are currently in the lobby are:"
				+ arrayToLine(serverMessage));
	}

	/**
	 * This method accepts the Server.INVITE packet sent by the Server. When
	 * this method is called, it adds the inviter (and to an inviterlist, and
	 * potentially, the custom board size. If the player isn't ingame, it will
	 * also show the Client that they have been invited by that Client.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	//@ requires serverMessage[0].equals(Server.INVITE);
	private void invite(String[] serverMessage) {
		String opponentName = serverMessage[1];
		if (serverMessage.length == 2) {
			addServerInvite(opponentName);
			if (!isIngame) {
				mui.addMessage("[INVITE]"
						+ opponentName
						+ " has invited you to a game of Connect4 (default boardsize)!");
				mui.addMessage("Use \"ACCEPT " + opponentName
						+ "\" to accept this invite or \"DECLINE "
						+ opponentName + "\" to decline it.");
			}
		} else if (serverMessage.length >= 4) {
			try {
				int boardX = Integer.parseInt(serverMessage[2]);
				int boardY = Integer.parseInt(serverMessage[3]);
				addServerInvite(opponentName, boardX, boardY);
				if (!isIngame) {
					mui.addMessage("[INVITE]"
							+ opponentName
							+ " has invited you to a game of Connect4 with a custom Board size of "
							+ boardX + " x " + boardY + "!");
					mui.addMessage("Use \"ACCEPT " + opponentName
							+ "\" to accept this invite or \"DECLINE "
							+ opponentName + "\" to decline it.");
				}
			} catch (NumberFormatException e) {
				mui.addMessage("[ERROR]The server just sent an invite with an invalid custom board size.");
				sendMessage(ERROR
						+ " "
						+ INVITE
						+ " Your server just sent me an invite with an invalid custom board size :(");
			}
		}
	}

	/**
	 * This method accepts the Server.DECLINE_INVITE packet. If the Server
	 * specified a person, the person will be removed from the list of people
	 * this Client has invited.
	 * 
	 * @param serverMessage
	 *            The full messsage the server sent.
	 */
	private void declineInvite(String[] serverMessage) {
		if (serverMessage.length > 1) {
			invited.remove(serverMessage[1]);
			mui.addMessage("[INVITE]The invite you sent to " + serverMessage[1]
					+ " got declined.");
		} else {
			mui.addMessage("[INVITE]The server just tried to decline one of your invites, but it didn't send who declined yours.");
			sendMessage(ERROR + " " + serverMessage[0]
					+ " Your server didn't send me who declined the invite.");
		}
	}

	/**
	 * This method accepts the Server.GAME_START packet sent by the Server. When
	 * this method is called, it will show the Client that a the game is
	 * started. The Client is set to being in-game, and a new Board is created.
	 * The size of the Board is dependant on the size sent in the invite (the
	 * Boardsizes of the invites are saved in a HashMap).
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	/*@ requires serverMessage[0].equals(Server.GAME_START);
	 	ensures board != null;
	 	ensures this.isIngame;
	 	ensures currPlayer == null;
	 */
	private void gameStart(String[] serverMessage) {
		firstPlayer = serverMessage[1];
		secondPlayer = serverMessage[2];

		if (firstPlayer.equals(getClientName())) {
			mui.addMessage("[GAME]A game between you and " + secondPlayer
					+ " has started!");
			Integer[] boardSize = invitedBy.get(secondPlayer);

			board = new Board(boardSize[1], boardSize[0]);
		} else {
			mui.addMessage("[GAME]A game between you and " + firstPlayer
					+ " has started!");
			Integer[] boardSize = invited.get(firstPlayer);
			board = new Board(boardSize[1], boardSize[0]);
		}

		this.isIngame = true;
		currPlayer = null; // Not set yet.
		// DEFINITION: currPlayer == 0 > Disc.YELLOW, currPlayer ==
		// 1 > Disc.RED
		mui.addMessage(board.toString());
		mui.addMessage("[GAME]You are YELLOW");
	}

	/**
	 * This method accepts the Server.GAME_END packet sent by the Server. When
	 * this method is called, it will set the Client to no longer being in-game.
	 * It will also show the client who won the game, or if the game was a draw.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	/*@	requires serverMessage[0].equals(Server.GAME_END);
	 	ensures !this.isIngame;
	 */
	private void gameEnd(String[] serverMessage) {
		this.isIngame = false;
		if (serverMessage.length > 2) {
			mui.addMessage("[GAME]The winner is: " + serverMessage[2]);
		} else if (serverMessage.length == 2) {
			if (serverMessage[1].equals(Game.DRAW)) {
				mui.addMessage("[GAME]The game was a draw!");
			} else {
				mui.addMessage("[GAME]The game has ended. Reason:"
						+ arrayToLine(serverMessage));
			}
		}
	}

	/**
	 * This method accepts the Server.MOVE packet sent by the Server. When this
	 * method is called, it will request a move from the Player. If the Player
	 * is a HumanPlayer, the GameView will be used to ask for a move. If the
	 * Player is a ComputerPlayer, the determineMove() method from the
	 * ComputerPlayer is used instead.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	//@ requires serverMessage[0].equals(Server.REQUEST_MOVE);
	private void requestMove(String[] serverMessage) {
		if (currPlayer == null) {
			currPlayer = firstPlayer;
		}
		if (localPlayer instanceof HumanPlayer) {
			localPlayer.determineMove(board);
		} else {
			int move = localPlayer.determineMove(board);
			sendMessage(MOVE + " " + move);
		}
	}

	/**
	 * This method accepts the Server.MOVE_OK packet sent by the Server. When
	 * this method is called, it will update the Board by inserting the Disc for
	 * the Player that was given in the packet. If it can't insert the Disc, it
	 * will request the Board and try to insert the Disc once again.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	//@ requires serverMessage[0].equals(Server.MOVE_OK);
	private synchronized void moveOK(String[] serverMessage) {
		if (currPlayer == null) {
			currPlayer = secondPlayer;
		}
		int move = -1;
		if (currPlayer.equals(firstPlayer)) {
			try {
				move = Integer.parseInt(serverMessage[2]);
			} catch (NumberFormatException e) {
				mui.addMessage("[ERROR]Server did not send a valid move. TERMINATING.");
				sendMessage(ERROR + " " + Server.MOVE_OK
						+ " You didn't send a valid move.");
				shutdown();
			}
			if (board.isField(move) && board.isEmptyField(move)) {
				board.insertDisc(move, Disc.YELLOW);
				currPlayer = secondPlayer;
			} else {
				if (!requestedBoard) {
					requestBoard();
					requestedBoard = true;
					try {
						wait();
						mui.addMessage("[BOARD]This is the board the server has: ");
						mui.addMessage(board.toString());
						moveOK(serverMessage);
					} catch (InterruptedException e) {
						mui.addMessage("[ERROR]Interrupted. TERMINATING.");
						sendMessage(ERROR + " " + Server.BOARD
								+ " My client got interrupted.");
						shutdown();
					}
				} else {
					mui.addMessage("[ERROR]Can't make the move on both the local board, and the board on the server. TERMINATING.");
					sendMessage(ERROR
							+ " "
							+ Server.BOARD
							+ " I can't make the specified move on the local board, and the Board you just sent me. TERMINATING.");
					shutdown();
				}
			}
		} else if (currPlayer.equals(secondPlayer)) {
			try {
				move = Integer.parseInt(serverMessage[2]);
			} catch (NumberFormatException e) {
				mui.addMessage("[ERROR]Server did not send a valid move. TERMINATING.");
				sendMessage(ERROR + " " + Server.MOVE_OK
						+ " You didn't send a valid move.");
				shutdown();
			}
			if (board.isField(move) && board.isEmptyField(move)) {
				board.insertDisc(move, Disc.RED);
				currPlayer = firstPlayer;
			} else {
				if (!requestedBoard) {
					requestBoard();
					requestedBoard = true;
					try {
						wait();
						moveOK(serverMessage);
					} catch (InterruptedException e) {
						mui.addMessage("[ERROR]Interrupted. TERMINATING.");
						sendMessage(ERROR + " " + Server.BOARD
								+ " My client got interrupted.");
						shutdown();
					}
				} else {
					mui.addMessage("[ERROR]Can't make the move on both the local board, and the board on the server. TERMINATING.");
					sendMessage(ERROR
							+ " "
							+ Server.BOARD
							+ " I can't make the specified move on the local board, and the Board you just sent me. TERMINATING.");
					shutdown();
				}
			}
		}
		mui.addMessage(board.toString());
	}

	/**
	 * This method sends a message to the ClientHandler using the OutputStream
	 * out.
	 * 
	 * @param msg
	 *            The message to be sent.
	 */
	//@ requires msg != null;
	public void sendMessage(String msg) {
		try {
			out.write(msg);
			out.newLine();
			out.flush();
		} catch (IOException e) {
			shutdown();
		}
	}

	/**
	 * This method closes the Socket connection and exits the program. On a side
	 * note, before it does this, it also sets the loop and isIngame variables
	 * for this Client to false.
	 */
	public void shutdown() {
		loop = false;
		isIngame = false;
		try {
			sock.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
		System.exit(0);
	}

	/**
	 * This method returns the name of this Client.
	 */
	/*@ pure */public String getClientName() {
		return clientName;
	}

	/**
	 * This method sets the name for this Client.
	 * 
	 * @param name
	 *            The name this Client should have.
	 */
	//@ ensures getClientName().equals(name);
	public void setClientName(String name) {
		clientName = name;
	}

	/**
	 * This method makes a Board out of the packet the server sends when the
	 * Board is requested.
	 * 
	 * @param line
	 *            The Boardpacket the Server sent.
	 * @return A new Board object with the Board as sent by the Server.
	 */
	//@ requires line != null;
	public Board toBoard(String line) {
		String[] protocol = line.split(" ");
		Board test = null;
		try {
			int boardColumns = Integer.parseInt(protocol[1]);
			int boardRows = Integer.parseInt(protocol[2]);

			test = new Board(boardRows, boardColumns);
			int i = 3;
			for (int row = boardRows - 1; row >= 0; row--) {
				for (int col = 0; col < boardColumns; col++) {
					if (Integer.parseInt(protocol[i]) == 0) {
						//Disc.EMPTY
						test.setField(row, col, Disc.EMPTY);
					} else if (Integer.parseInt(protocol[i]) == 1) {
						//Disc.YELLOW
						test.setField(row, col, Disc.YELLOW);
					} else if (Integer.parseInt(protocol[i]) == 2) {
						//Disc.RED
						test.setField(row, col, Disc.RED);
					}
					i++;
				}
			}

		} catch (NumberFormatException e) {
			mui.addMessage("[ERROR]Server sent a wrong board. TERMINATING.");
			sendMessage(ERROR + " " + Server.BOARD
					+ " You sent me an invalid Board. TERMINATING.");
			shutdown();
		}
		return test;
	}

	/**
	 * This method is used to convert an Stringarray to a single String.
	 * 
	 * @param array
	 *            The array to convert.
	 * @return The array converted to one line.
	 */
	//@ requires array != null;
	public String arrayToLine(String[] array) {
		String retLine = "";
		for (int i = 1; i < array.length; i++) {
			retLine += " " + array[i];
		}
		return retLine;
	}

	/**
	 * Method to request the board from the server.
	 */
	private void requestBoard() {
		sendMessage(REQUEST_BOARD);
	}

	/**
	 * Method to add an invite to the list of people this Client has invited.
	 * 
	 * @param name
	 *            The name this Client just invited.
	 */
	public void addClientInvite(String name) {
		addClientInvite(name, 7, 6);
	}

	/**
	 * Method to add an invite to the list of people this Client has invited
	 * with a custom Board size.
	 * 
	 * @param name
	 *            The name this Client just invited.
	 * @param BoardX
	 *            The custom Board size's X value.
	 * @param BoardY
	 *            The custom Board size's Y value.
	 */
	public void addClientInvite(String name, int BoardX, int BoardY) {
		invited.put(name, new Integer[] { BoardX, BoardY });
	}

	/**
	 * Method to add an invite to the list of people this Client has been
	 * invited by.
	 * 
	 * @param name
	 *            The name this Client just got invited by.
	 */
	public void addServerInvite(String name) {
		addServerInvite(name, 7, 6);
	}

	/**
	 * Method to add an invite to the list of people this Client has been
	 * invited by with a custom Board size.
	 * 
	 * @param name
	 *            The name this Client just got invited by.
	 * @param BoardX
	 *            The custom Board size's X value.
	 * @param BoardY
	 *            The custom Board size's Y value.
	 */
	public void addServerInvite(String name, int BoardX, int BoardY) {
		invitedBy.put(name, new Integer[] { BoardX, BoardY });
	}

	/**
	 * Method to remove an invite from the list of people this client has
	 * invited. It's called when the server sends a Server.DECLINE_INVITE
	 * packet.
	 * 
	 * @param name
	 *            The name of the person who declined the invite.
	 */
	public void removeServerInvite(String name) {
		invited.remove(name);
	}

	/**
	 * If the server sent a valid Leaderboard, this method adds the formatted
	 * leaderboard to the View.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	public void showLeaderBoard(String[] serverMessage) {
		// EXAMPLE: LEADERBOARD REQUEST_BOARD 1 0 1 1 WinPlayer 1 0 1 2 LosePlayer 0 1 1 3 SmartPlayer 0 1 1 4
		// DELEN DOOR 4, dat is aantal Clients dat je moet listen
		// If it is a valid leaderboard
		if ((serverMessage.length - 1) % 5 == 0) {
			int amountOfPlayers = (serverMessage.length - 1) / 5;
			for (int i = 0; i < amountOfPlayers; i++) {
				mui.addMessage(serverMessage[((i * 5) + 5)] + ". "
						+ serverMessage[((i * 5) + 1)] + " Wins: "
						+ serverMessage[((i * 5) + 2)] + " Draws: "
						+ serverMessage[((i * 5) + 3)] + " Losses: "
						+ serverMessage[((i * 5) + 4)]);
			}
		} else {
			mui.addMessage("[ERROR]Didn't get a valid Leaderboard from the Server.");
			sendMessage(ERROR + " " + Server.LEADERBOARD
					+ " Didn't get a valid Leaderboard from your Server :(");
		}
	}

	public void setPlayer(Player player) {
		localPlayer = player;
	}

	public String askName() {
		return mui.getName();
	}

	public void setUpPlayer() {
		String[] splitName = getClientName().split("\\s+");
		if (splitName[0].equals("-N")) {
			if (splitName.length == 1) {
				setClientName("NaivePlayer");
				setPlayer(new ComputerPlayer(Disc.YELLOW, new NaiveStrategy()));
			} else {
				setClientName(splitName[1]);
				setPlayer(new ComputerPlayer(Disc.YELLOW, new NaiveStrategy()));
			}
		} else if (splitName[0].equals("-S")) {
			if (splitName.length == 1) {
				setClientName("SmartPlayer");
				setPlayer(new ComputerPlayer(Disc.YELLOW, new SmartStrategy()));
			} else {
				setClientName(splitName[1]);
				setPlayer(new ComputerPlayer(Disc.YELLOW, new SmartStrategy()));
			}
		} else {
			setClientName(splitName[0]);
			setPlayer(new HumanPlayer(Disc.YELLOW, mui));
		}
	}

	public void setUpIP() {
		this.host = mui.askHost();
	}

	public void setUpPort() {
		this.port = mui.askPort();
	}
}
